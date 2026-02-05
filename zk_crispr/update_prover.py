import os

def replace_mixed(file_path, target, first_values, remaining_replacement):
    # 1. Check if file exists
    if not os.path.exists(file_path):
        print(f"Error: The file '{file_path}' was not found.")
        return

    try:
        # 2. Open the file
        with open(file_path, 'r', encoding='utf-8') as file:
            content = file.read()

        if target not in content:
            print(f"No occurrences of '{target}' found in {file_path}.")
            return

        # 3. Stage 1: Replace using the specific list (FIRST_VALUES)
        list_count = 0
        for val in first_values:
            # Check if we still have targets to replace
            if target in content:
                replacement_string = f'"{val}"'
                # Replace only the FIRST occurrence found
                content = content.replace(target, replacement_string, 1)
                list_count += 1
            else:
                break

        # 4. Stage 2: Replace ALL remaining targets with the default value
        remaining_count = content.count(target)
        if remaining_count > 0:
            content = content.replace(target, remaining_replacement)

        # 5. Write the changes back
        with open(file_path, 'w', encoding='utf-8') as file:
            file.write(content)

        print(f"Done.")
        print(f"- Replaced first {list_count} occurrences with values from list.")
        print(f"- Replaced remaining {remaining_count} occurrences with '{remaining_replacement}'.")

    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    # Configuration
    FILE_NAME = "Prover.toml"

    # Values for the first N replacements
    FIRST_VALUES = [
        "0", "0", "0", "0", "2", "1", "0", "3", "2", "1",
        "0", "3", "2", "1", "0", "3", "2", "1", "0", "3",
        "2", "3", "0", "3", "0", "2", "2", "0", "2", "2"
    ]

    SEARCH_TEXT = '""'

    # Value for all subsequent replacements (after the list is exhausted)
    REPLACE_TEXT = '"3"'

    replace_mixed(FILE_NAME, SEARCH_TEXT, FIRST_VALUES, REPLACE_TEXT)