# Wrote this code to verify that fixed point arithmetic matches correctly.

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

if __name__ == "__main__":
    # Example usage
    noir_output = "(0x01000000a1c4023c01, 0x0100418d54a326b3f6)"
    l2_loss, ss_pred = parse_noir_output(noir_output)
    print(l2_loss, ss_pred)  # Should print the corresponding float values

    r_squared = 1 - (l2_loss / ss_pred)
    print(f"R² score from Noir output: {r_squared:.6f}")
