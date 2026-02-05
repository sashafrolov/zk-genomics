import os
import sys

def replace_in_file(file_path, target, replacement):
    # 1. Check if file exists to prevent crashing
    if not os.path.exists(file_path):
        print(f"Error: The file '{file_path}' was not found in the current directory.")
        return

    try:
        # 2. Open the file in read mode
        with open(file_path, 'r', encoding='utf-8') as file:
            content = file.read()

        # 3. Check if the target exists before writing (optimization)
        if target not in content:
            print(f"No occurrences of '{target}' found in {file_path}.")
            return

        # 4. Perform the replacement
        new_content = content.replace(target, replacement)

        # 5. Write the changes back to the file
        with open(file_path, 'w', encoding='utf-8') as file:
            file.write(new_content)
            
        print(f"Success: Replaced all occurrences of '{target}' with '{replacement}' in {file_path}.")

    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    # Configuration
    FILE_NAME = "Prover.toml"
    SEARCH_TEXT = '""'
    REPLACE_TEXT = '"3"'
    
    replace_in_file(FILE_NAME, SEARCH_TEXT, REPLACE_TEXT)
