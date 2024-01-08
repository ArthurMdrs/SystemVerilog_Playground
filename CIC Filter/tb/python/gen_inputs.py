import numpy as np
import matplotlib.pyplot as plt
import random

from definitions import *

# Change to 1 if you want to plot the wave
plot = 0

# Fundamental frequency in radians/s
# w0 = 2*np.pi*f0

# Define time vector
t = np.arange(t_start, t_end, Ts)

# Set rng seed
# random.seed(18)
random.seed()

# Generate waveform
wave_out = np.zeros(len(t))
wave_out = generate_wave(wave_type, t)

# Shift the wave up so we don't get negative values
wave_out -= min(wave_out)

# Make sure result fits in 8 bits
for i in range(len(wave_out)):
    if wave_out[i] > 255:
        wave_out[i] = 255

wave_out_int = []
input_file = open("input.txt", "w")
for i in wave_out:
    # print(i)
    wave_out_int.append(int(i))
    input_file.write(str(int(i)) + "\n")
input_file = open("input.txt", "rb+")
input_file.seek(-1,2)
input_file.truncate()

if plot:
    plt.stem(t,wave_out_int)
    plt.show()