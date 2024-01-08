import numpy as np
import random
import sys

# Read command line args
n_args = len(sys.argv)
print("This file is "+sys.argv[0])
DnI = int(sys.argv[1])
stages = int(sys.argv[2])
rate = int(sys.argv[3])
print(stages, " stages, ", "rate = ", rate)

# Fundamental frequency
f0 = 100 # Hz
w0 = 2*np.pi*f0
max_harmonic = 5

# Sampling frequency and period
if (DnI == 1):
    fs = 16*max_harmonic*f0 # hz
if (DnI == 0):
    fs = 4*max_harmonic*f0 # hz
Ts = 1/fs # s

# Define time limits
n_periods = 4
t_start = 0 # s
t_end = n_periods/f0 # s

# Select type of waveform
options = ["sum_hmncs", "sine", "impulse"]
wave_type = options[0]

def generate_wave(wave_type="sum_of_harmonics", t=0):
    wave_out = np.zeros(len(t))
    A_max = 260/2

    if (wave_type == options[0]): # Sum of harmonics
        for i in range(1, max_harmonic+1):
            A = random.randint(1, A_max) / i
            # theta = random.random() * 2*np.pi
            theta = 0
            wave_out += A * np.sin(i*w0*t + theta)
            print("Amp["+str(i)+"] = "+str(A))
    
    if (wave_type == options[1]): # Pure sine
        theta = random.random() * 2*np.pi
        wave_out = A_max * np.sin(w0*t + theta)

    if (wave_type == options[2]): # Impulse
        wave_out[0] = A_max

    return wave_out