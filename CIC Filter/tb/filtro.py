from math import pi
import numpy as np
import matplotlib.pyplot as plt


sample_rate = 150 # hz
start_time = 0 # s
end_time = 1 # s

time = np.arange(start_time, end_time, 1/sample_rate)

theta = 0


frequency = [3,5,2,1,10]
amplitude = [1,2,7,3,.1]
sinwave = 0

for i in range(len(amplitude)):
    sinwave += (5 + amplitude[i]*(np.sin(2*np.pi*frequency[i]*time+theta)))
  
#plt.subplot(5,1,1)
#plt.plot(time,sinwave)
#plt.subplot(2,1,1)
#plt.stem(time,sinwave)
# SINWAVE = np.fft.fft(sinwave)
#plt.subplot(5,1,3)
#freq = np.fft.fftfreq(sample_rate)
#plt.stem(freq, abs(SINWAVE))
sinwave_int = []
input_file = open("input.txt", "w")
for i in sinwave:
    print(((i)))
    sinwave_int.append(int(i))
    input_file.write(str(int(i)) + "\n")
input_file = open("input.txt", "rb+")
input_file.seek(-1,2)
input_file.truncate()

plt.subplot(2,1,1)
plt.stem(time,sinwave_int)
# plt.show()

sinwave_filter = []
output_file = open("output.txt", "r")
for i in output_file:
    print(int(i))
    if(int(i) == 0):
        sinwave_filter.append(0)
    else:
        sinwave_filter.append(int(i)-5)

plt.subplot(2,1,2)
plt.stem(time,sinwave_filter)
# plt.show()
