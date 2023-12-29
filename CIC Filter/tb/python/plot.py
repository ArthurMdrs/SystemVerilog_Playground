import numpy as np
import matplotlib.pyplot as plt
import random

from definitions import *

# Define t vector
t = np.arange(t_start, t_end, Ts)

x_in = []
y_out =[]
with open("input.txt") as input_file:
    for i in input_file:
        x_in.append(int(i))

with open("output.txt") as output_file:
    try:
        for i in output_file:
            y_out.append((int(i)))
    except ValueError:
        print("tratament")

plt.figure(1, figsize=(18,9))
# plt.suptitle("Before and after CIC filter", size="x-large")
plt.subplot(3,1,1)
plt.title("Before CIC filter")
plt.stem(t, x_in)
plt.subplot(3,1,2)
plt.title("After CIC filter")
plt.stem(t, y_out, 'r', markerfmt = 'ro')
plt.subplot(3,1,3)
plt.title("Comparison")
plt.stem(t, x_in)
plt.stem(t, y_out, 'r', markerfmt = 'ro')
plt.tight_layout()
# plt.savefig("my_fig.png")
plt.savefig(wave_type+".png")
plt.show()

