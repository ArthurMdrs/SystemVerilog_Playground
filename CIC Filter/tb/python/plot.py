import numpy as np
import matplotlib.pyplot as plt

from definitions import *

# Read input file
in_vec = []
with open("input.txt") as input_file:
    for i in input_file:
        in_vec.append(int(i))

# Read output file
out_vec = []
with open("output.txt") as output_file:
    try:
        for i in output_file:
            out_vec.append(int(i))
    except ValueError:
        print("Error")

# Adjust original wave vector in case of interpolation
if DnI == 0:
    aux_vec = [0] * rate*len(in_vec)
    for i in range(len(in_vec)):
        for j in range(rate):
            aux_vec[rate*i+j] = in_vec[i]
    in_vec = aux_vec

# Adjust filtered wave vector to the same size as in_vec
n_samples = len(in_vec)
out_vec = out_vec[-n_samples:]

# Define time vector
Ts = (t_end-t_start)/n_samples
t = np.arange(t_start, t_end, Ts)



# Plots in time domain
plt.figure(1, figsize=(18,9))

plt.subplot(3,1,1)
plt.title("Before CIC filter")
plt.plot(t, in_vec, drawstyle="steps-pre")
plt.xlabel("Time (s)")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.subplot(3,1,2)
plt.title("After CIC filter")
plt.plot(t, out_vec, 'r', drawstyle="steps-pre")
plt.xlabel("Time (s)")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.subplot(3,1,3)
plt.title("Comparison")
plt.plot(t, in_vec, drawstyle="steps-pre")
plt.plot(t, out_vec, 'r', drawstyle="steps-pre")
plt.legend(["Original", "Filtered"])
plt.xlabel("Time (s)")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.tight_layout()
plt.savefig("png/"+wave_type+"_ST="+str(stages)+"_RT="+str(rate)+"_time.png")
# plt.show()



# Adjust fs to rate*fs in case of interpolation
if (DnI == 0):
    fs = fs * rate

# Get frequency decomposition of both signals
# Obs1: dividing by n_samples = multiplying by dt
# Obs2: multiply by 2 to account for negative side of Fourier Transform
in_fft = abs(np.fft.fft(in_vec)) / n_samples * 2
out_fft = abs(np.fft.fft(out_vec)) / n_samples * 2
f = np.linspace(0, fs, n_samples)

# Print values of DC offset and original harmonics
for i in range(0, max_harmonic+1):
    print(i*100, " Hz values: ", in_fft[i*n_periods], " and ", out_fft[i*n_periods])

# Ignore DC value for logarithmic plot
in_fft = in_fft[n_periods-1:]
out_fft = out_fft[n_periods-1:]
f = f[n_periods-1:]

# Plots in frequency domain
plt.figure(2, figsize=(18,9))

plt.subplot(2,1,1)
plt.semilogx(f, in_fft, marker = 'o')
plt.title("Before CIC filter")
plt.xlabel("Frequency (Hz)")
plt.ylabel("Magnitude (abs)")
plt.grid(visible=True, which="both")

plt.subplot(2,1,2)
plt.semilogx(f, out_fft, 'r', marker = 'o')
plt.title("After CIC filter")
plt.xlabel("Frequency (Hz)")
plt.ylabel("Magnitude (abs)")
plt.grid(visible=True, which="both")

plt.tight_layout()
plt.savefig("png/"+wave_type+"_ST="+str(stages)+"_RT="+str(rate)+"_freq.png")
# plt.show()
