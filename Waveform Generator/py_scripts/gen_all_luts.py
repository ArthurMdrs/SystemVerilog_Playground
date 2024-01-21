import subprocess

valid_args = ["sine", "sawtooth", "triangular"]

script_path = "./gen_lut.py"

for arg in valid_args:
    subprocess.run(['python3', script_path, arg])