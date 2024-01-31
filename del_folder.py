import sys
import os
import shutil

folder_name = sys.argv[1]

def remove_folder():
    # Verify if the folder exists
    if not os.path.exists(folder_name):
        print(f"The folder '{folder_name}' does not exist.")
        return

    # Ask for confirmation
    confirmation = input(f"Do you want to remove the folder '{folder_name}' and its contents? (y/n): ")

    # Check user input
    if confirmation.lower() == 'y':
        try:
            # Use shutil.rmtree() to remove the folder and its contents
            shutil.rmtree(folder_name)
            print(f"The folder '{folder_name}' and its contents have been successfully removed.")
        except Exception as e:
            print(f"An error occurred: {e}")
    else:
        print(f"The folder '{folder_name}' has not been removed.")

if __name__ == "__main__":
    remove_folder()