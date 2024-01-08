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

print(len(in_vec))
print(len(out_vec))
# n_samples = len(in_vec)
# if DnI == 1:
#     n_samples = len(in_vec)
#     out_vec = out_vec[-n_samples:]
if DnI == 0:
    aux_vec = [0] * rate*len(in_vec)
    for i in range(len(in_vec)):
        for j in range(rate):
            aux_vec[rate*i+j] = in_vec[i]
    in_vec = aux_vec
n_samples = len(in_vec)
out_vec = out_vec[-n_samples:]

# Define time vectors
Ts = (t_end-t_start)/n_samples
t1 = np.arange(t_start, t_end, Ts)
t2 = np.arange(t_start, t_end, Ts)

# Define time vectors
# Ts1 = (t_end-t_start)/len(in_vec)
# t1 = np.arange(t_start, t_end, Ts1)
# Ts2 = (t_end-t_start)/len(out_vec)
# t2 = np.arange(t_start, t_end, Ts2)
# t2 = t2[0:len(out_vec)]

# Define time vectors
# Ts = (t_end-t_start)/len(in_vec)
# t1 = np.arange(t_start, t_end, Ts)
# diff = len(out_vec) - len(in_vec)
# t2 = np.arange(t_start, (t_end + diff*Ts), Ts)


#   DONE!!!!
# Change linestyle of plots or go back to plt.stem

# Plots in time domain
plt.figure(1, figsize=(18,9))
# plt.suptitle("Before and after CIC filter", size="x-large")

plt.subplot(3,1,1)
plt.title("Before CIC filter")
# plt.stem(t1, in_vec)
plt.plot(t1, in_vec, drawstyle="steps-mid")
plt.xlabel("Time (s)")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.subplot(3,1,2)
plt.title("After CIC filter")
# plt.stem(t2, out_vec, 'r', markerfmt = 'ro')
plt.plot(t2, out_vec, 'r', drawstyle="steps-mid")
plt.xlabel("Time (s)")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.subplot(3,1,3)
plt.title("Comparison")
# plt.stem(t1, in_vec)
plt.plot(t1, in_vec, drawstyle="steps-mid")
# plt.stem(t2, out_vec, 'r', markerfmt = 'ro')
plt.plot(t2, out_vec, 'r', drawstyle="steps-mid")
plt.legend(["Original", "Filtered"])
plt.xlabel("Time (s)")
plt.ylabel("Amplitude")
plt.grid(visible=True, which="both")

plt.tight_layout()
if n_args == 4:
    plt.savefig("png/"+wave_type+"_ST="+str(stages)+"_RT="+str(rate)+"_time.png")
else:
    plt.savefig("png/"+wave_type+"_time.png")
# plt.show()





# ATTENTION!!! NEEDS FIXING!!!
# Adjust fs to rate*fs in case of interpolation!!
if (DnI == 0):
    fs = fs * rate



#   DONE!!!!
# See about magnitude normalization of fft!!


# Get frequency decomposition of both signals
# Obs1: dividing by n_samples = multiplying by dt
# Obs2: multiply by 2 to account for negative side of Fourier Transform
in_fft = abs(np.fft.fft(in_vec)) / n_samples * 2
f1 = np.linspace(0, fs, len(in_fft))

# while out_vec[0] == 0:
#     out_vec = out_vec[1:]
out_fft = abs(np.fft.fft(out_vec)) / n_samples * 2
f2 = np.linspace(0, fs, len(out_fft))

# Print values of DC offset and original harmonics
for i in range(0, max_harmonic+1):
    print(i*100, " Hz values: ", in_fft[i*n_periods], " and ", out_fft[i*n_periods])

# Ignore DC value for logarithmic plot
in_fft = in_fft[n_periods-1:]
f1 = f1[n_periods-1:]
out_fft = out_fft[n_periods-1:]
f2 = f2[n_periods-1:]

# Plots in frequency domain
plt.figure(2, figsize=(18,9))
plt.subplot(2,1,1)
plt.semilogx(f1, in_fft, marker = 'o')
# plt.plot(f1, in_fft, marker = 'o')
plt.title("Before CIC filter")
plt.xlabel("Frequency (Hz)")
plt.ylabel("Magnitude (abs)")
plt.grid(visible=True, which="both")
# plt.ylim(top=max(in_fft)/2)

plt.subplot(2,1,2)
plt.semilogx(f2, out_fft, 'r', marker = 'o')
plt.title("After CIC filter")
plt.xlabel("Frequency (Hz)")
plt.ylabel("Magnitude (abs)")
plt.grid(visible=True, which="both")
# plt.ylim(top=max(out_fft)/2)

plt.tight_layout()
if n_args == 4:
    plt.savefig("png/"+wave_type+"_ST="+str(stages)+"_RT="+str(rate)+"_freq.png")
else:
    plt.savefig("png/"+wave_type+"_freq.png")
# plt.show()
