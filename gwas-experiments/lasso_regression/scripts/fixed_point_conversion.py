# Wrote this code to verify that fixed point arithmetic matches correctly.

import re
import pathlib

# Fixed-point constants matching main.nr
FIXED_POINT_PRECISION_BYTES = 4
FIXED_POINT_MAX_MAGNITUDE_BYTES = 4
FIXED_POINT_SCALE = 2 ** (FIXED_POINT_PRECISION_BYTES * 8)  # 2^32
FIXED_POINT_ZERO = 2 ** ((FIXED_POINT_PRECISION_BYTES + FIXED_POINT_MAX_MAGNITUDE_BYTES) * 8)  # 2^64


def from_fixed_point(hex_str: str) -> float:
    """
    Convert a Noir hex string (e.g., '0x01000000a1c4023c01') back to a Python float.
    Reverses the fixed-point encoding: (value - FIXED_POINT_ZERO) / FIXED_POINT_SCALE
    """
    value = int(hex_str, 16)
    unbiased = value - FIXED_POINT_ZERO
    return unbiased / FIXED_POINT_SCALE


def parse_noir_output(output: str) -> list[float]:
    """
    Parse Noir circuit output like '(0x01000000a1c4023c01, 0x0100418d54a326b3f6)'
    and return a list of Python floats.
    """
    output = output.strip().strip('()')
    hex_values = [s.strip() for s in output.split(',')]
    return [from_fixed_point(h) for h in hex_values]


def parse_output_log(log_path: pathlib.Path) -> list[dict]:
    """
    Parse output.log and extract paired Python and circuit values for each iteration.
    Returns a list of dicts with python_r2, python_l2, circuit_l2, circuit_ss_pred, circuit_r2.
    """
    content = log_path.read_text()

    # Regex patterns
    r2_pattern = re.compile(r'R Squared score: ([\d.]+)')
    l2_pattern = re.compile(r'L2 loss \(SSE\): ([\d.]+)')
    circuit_pattern = re.compile(r'Circuit output: \(([^)]+)\)')

    # Find all matches
    r2_matches = r2_pattern.findall(content)
    l2_matches = l2_pattern.findall(content)
    circuit_matches = circuit_pattern.findall(content)

    results = []
    n_iterations = min(len(r2_matches), len(l2_matches), len(circuit_matches))

    for i in range(n_iterations):
        python_r2 = float(r2_matches[i])
        python_l2 = float(l2_matches[i])

        # Parse circuit output: (l2_loss, ss_pred, auth_hash)
        hex_values = [s.strip() for s in circuit_matches[i].split(',')]
        circuit_l2 = from_fixed_point(hex_values[0])
        circuit_ss_pred = from_fixed_point(hex_values[1])
        circuit_r2 = 1 - (circuit_l2 / circuit_ss_pred) if circuit_ss_pred != 0 else 0

        results.append({
            'python_r2': python_r2,
            'python_l2': python_l2,
            'circuit_l2': circuit_l2,
            'circuit_ss_pred': circuit_ss_pred,
            'circuit_r2': circuit_r2,
        })

    return results


def compute_statistics(results: list[dict]) -> dict:
    """
    Compute average differences (magnitude and percentage) for R² and L2 loss.
    """
    if not results:
        return {}

    r2_abs_diffs = []
    r2_pct_diffs = []
    l2_abs_diffs = []
    l2_pct_diffs = []

    for r in results:
        # R² differences
        r2_abs = abs(r['python_r2'] - r['circuit_r2'])
        r2_abs_diffs.append(r2_abs)
        if r['python_r2'] != 0:
            r2_pct_diffs.append(100 * r2_abs / abs(r['python_r2']))

        # L2 loss differences
        l2_abs = abs(r['python_l2'] - r['circuit_l2'])
        l2_abs_diffs.append(l2_abs)
        if r['python_l2'] != 0:
            l2_pct_diffs.append(100 * l2_abs / abs(r['python_l2']))

    return {
        'n_iterations': len(results),
        'r2_avg_abs_diff': sum(r2_abs_diffs) / len(r2_abs_diffs),
        'r2_avg_pct_diff': sum(r2_pct_diffs) / len(r2_pct_diffs) if r2_pct_diffs else 0,
        'l2_avg_abs_diff': sum(l2_abs_diffs) / len(l2_abs_diffs),
        'l2_avg_pct_diff': sum(l2_pct_diffs) / len(l2_pct_diffs) if l2_pct_diffs else 0,
    }


if __name__ == "__main__":
    # Path to output.log (in enclosing directory)
    log_path = pathlib.Path(__file__).parent.parent / "output2.log"

    if not log_path.exists():
        print(f"Error: {log_path} does not exist.")
        exit(1)

    print(f"Parsing {log_path}...")
    results = parse_output_log(log_path)

    if not results:
        print("No matching iterations found in the log.")
        exit(1)

    print(f"\nFound {len(results)} iterations.\n")

    # Print first few iterations as examples
    print("Sample comparisons (first 5 iterations):")
    print("-" * 80)
    for i, r in enumerate(results[:5]):
        print(f"Iteration {i + 1}:")
        print(f"  R² - Python: {r['python_r2']:.6f}, Circuit: {r['circuit_r2']:.6f}, "
              f"Diff: {abs(r['python_r2'] - r['circuit_r2']):.6e}")
        print(f"  L2 - Python: {r['python_l2']:.6f}, Circuit: {r['circuit_l2']:.6f}, "
              f"Diff: {abs(r['python_l2'] - r['circuit_l2']):.6e}")
    print("-" * 80)

    # Compute and print statistics
    stats = compute_statistics(results)

    print("\n===== Summary Statistics =====")
    print(f"Total iterations analyzed: {stats['n_iterations']}")
    print()
    print("R² (R Squared):")
    print(f"  Average absolute difference: {stats['r2_avg_abs_diff']:.6e}")
    print(f"  Average percentage difference: {stats['r2_avg_pct_diff']:.6f}%")
    print()
    print("L2 Loss (SSE):")
    print(f"  Average absolute difference: {stats['l2_avg_abs_diff']:.6e}")
    print(f"  Average percentage difference: {stats['l2_avg_pct_diff']:.6f}%")
