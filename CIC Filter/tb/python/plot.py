import numpy as np
import matplotlib.pyplot as plt
import random

from definitions import *

# Read input file
in_vec = []
with open("input.txt") as input_file:
    for i in input_file:
        in_vec.append(int(i))

# Read output file
out_vec =[]
with open("output.txt") as output_file:
    try:
        for i in output_file:
            out_vec.append(int(i))
    except ValueError:
        print("Error")

# Define time vectors
Ts = (t_end-t_start)/len(in_vec)
t1 = np.arange(t_start, t_end, Ts)
diff = len(out_vec) - len(in_vec)
t2 = np.arange(t_start, (t_end + diff*Ts), Ts)

# Plots
plt.figure(1, figsize=(18,9))
# plt.suptitle("Before and after CIC filter", size="x-large")
plt.subplot(3,1,1)
plt.title("Before CIC filter")
plt.stem(t1, in_vec)
plt.xlabel("Time")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.subplot(3,1,2)
plt.title("After CIC filter")
plt.stem(t2, out_vec, 'r', markerfmt = 'ro')
plt.xlabel("Time")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.subplot(3,1,3)
plt.title("Comparison")
plt.stem(t1, in_vec)
plt.stem(t2, out_vec, 'r', markerfmt = 'ro')
plt.legend(["Original", "Filtered"])
plt.xlabel("Time")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.tight_layout()
# plt.savefig("my_fig.png")
plt.savefig("png/"+wave_type+".png")
plt.show()

