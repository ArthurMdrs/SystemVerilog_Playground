import subprocess
import sys

this_path = sys.argv[0].rstrip("gen_all_luts.py")

valid_args = ["sine", "sawtooth", "triangular", "rectangular"]

script_path = this_path + "gen_lut.py"

for arg in valid_args:
    subprocess.run(['python3', script_path, arg])