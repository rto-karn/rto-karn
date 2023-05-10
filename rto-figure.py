import numpy as np
import matplotlib.pyplot as plt

# Constants
c = 60 + ((75 - 60) / 2)
r = (75 - 60) / 2
alpha = 1/8
beta = 1/4
rttvar0 = (r * 1.5)
srtt0 = 80

# Function definition for bound on SRTT
def f(x, y):
    return ((1 - alpha) ** (x + 1)) * srtt0 + y - ((1 - alpha) ** (x + 1)) * y

def srtt(prev_srtt, cur_sample):
    return (1 - alpha) * prev_srtt + alpha * cur_sample

def rttvar(prev_rttvar, prev_srtt, cur_sample):
    return (1 - beta) * prev_rttvar + beta * abs(prev_srtt - cur_sample)

# Generate 1000 random numbers from a uniform distribution over [60, 75]
y = np.random.uniform(60, 75, size=1000)

# Create an array of integers from 1 to 1000 as the x-axis values
x = np.arange(1, 1001)

srtts = [srtt0]
for i in range(len(y)):
    srtts.append((1-alpha) * srtts[i] + alpha * y[i])
rttvars = [rttvar0]
for i in range(len(y)):
    # srtts[i] as we didn't yet do [1:]
    rttvars.append((1-beta) * rttvars[i] + beta * abs(srtts[i] - y[i]))
rtos = []
for i in range(len(y)):
    rtos.append(srtts[i] + max(1, 4 * rttvars[i]))
rttvars = rttvars[1:]
srtts = srtts[1:]

# Begin by testing the property that, if |srtt - s| < Del for all srtt and s, 
# then rttvar[-1] <= compute_upper_bound_on_rttvar(Del).
Del = 0
for i in range(len(y)):
    prior_srtt = srtt0 if i == 0 else srtts[i - 1]
    innerDel = abs(prior_srtt - y[i])
    if innerDel > Del:
        Del = innerDel

g_values = []

for i in range(1, len(y)):
    # Claim: srtt_i <= f(i, c + r) for all i.
    if srtts[i] > f(i, c + r):
        print("Error with assumption about srtts.")
    # Claim: s_i in [c - r, c + r] for all i.
    if c + r < y[i] or c - r > y[i]:
        print("Error with assumption about samples bound.")
    ith_bound = f(i, c + r) - (c - r)
    # Claim: ith |f(i, c+r) - (c-r)| > all subsequent |srtt[k-1] - s[k]|.
    for k in range(i, len(y)):
        innerDel = abs(srtts[k - 1] - y[k])
        if innerDel > ith_bound:
            print("Problem with ith_bound, i=", i, "k=", k)
    # Compute the corresponding rttvar delta
    inner_n = (len(y) - i)
    rttvar_delta = ((1 - beta) ** inner_n) * rttvars[i - 1] + \
                   (1 - ((1 - beta) ** inner_n)) * ith_bound
    if rttvars[-1] > rttvar_delta:
        print("Problem with bound on last rttvar.")
    g_values.append(rttvar_delta)
    

fig, (ax1, ax2, ax3, ax4) = plt.subplots(4, 1, sharex=True, height_ratios=[4,1.5,4,1.5], dpi=150)
fig.subplots_adjust(hspace=0.05)  # adjust space between axes

# Create the scatter plot
ax1.scatter(x, y, label="$S_i$", alpha=0.8, color='tan')

# Plot functions
ax1.plot(x, f(x, c+r), label='$H$')
ax1.plot(x, f(x, c-r), label='$L$')
ax1.plot(x, rtos, label='RTO')
ax1.plot(x, srtts, label='SRTT', alpha=0.5)

ax2.plot(x, rttvars, label='RTTVar', color='red')
ax2.plot(x[1:], g_values, label='$\\Delta$', color='purple')


ax1.spines.bottom.set_visible(False)
ax2.spines.top.set_visible(False)
ax1.xaxis.tick_top()
ax1.tick_params(labeltop=False)  # don't put tick labels at the top
# ax2.xaxis.tick_bottom()

# Set axis labels and title
plt.xlabel('Number N of consecutive c/r steady-state samples')
plt.ylabel('ms')

d = .5  # proportion of vertical to horizontal extent of the slanted line
kwargs = dict(marker=[(-1, -d), (1, d)], markersize=12,
              linestyle="none", color='k', mec='k', mew=1, clip_on=False)
ax1.plot([0, 1], [0, 0], transform=ax1.transAxes, **kwargs)
ax2.plot([0, 1], [1, 1], transform=ax2.transAxes, **kwargs)

y = np.full((1000,), 60)  # create an array of 1000 points initialized to 60
y[::100] = 75  # set every 100th point to 75

srtts = [srtt0]
for i in range(len(y)):
    srtts.append((1-alpha) * srtts[i] + alpha * y[i])
rttvars = [rttvar0]
for i in range(len(y)):
    # srtts[i] as we didn't yet do [1:]
    rttvars.append((1-beta) * rttvars[i] + beta * abs(srtts[i] - y[i]))
rtos = []
for i in range(len(y)):
    rtos.append(srtts[i] + max(1, 4 * rttvars[i]))
rttvars = rttvars[1:]
srtts = srtts[1:]

# Begin by testing the property that, if |srtt - s| < Del for all srtt and s, 
# then rttvar[-1] <= compute_upper_bound_on_rttvar(Del).
Del = 0
for i in range(len(y)):
    prior_srtt = srtt0 if i == 0 else srtts[i - 1]
    innerDel = abs(prior_srtt - y[i])
    if innerDel > Del:
        Del = innerDel

g_values = []

for i in range(1, len(y)):
    # Claim: srtt_i <= f(i, c + r) for all i.
    if srtts[i] > f(i, c + r):
        print("Error with assumption about srtts.")
    # Claim: s_i in [c - r, c + r] for all i.
    if c + r < y[i] or c - r > y[i]:
        print("Error with assumption about samples bound.")
    ith_bound = f(i, c + r) - (c - r)
    # Claim: ith |f(i, c+r) - (c-r)| > all subsequent |srtt[k-1] - s[k]|.
    for k in range(i, len(y)):
        innerDel = abs(srtts[k - 1] - y[k])
        if innerDel > ith_bound:
            print("Problem with ith_bound, i=", i, "k=", k)
    # Compute the corresponding rttvar delta
    inner_n = (len(y) - i)
    rttvar_delta = ((1 - beta) ** inner_n) * rttvars[i - 1] + \
                   (1 - ((1 - beta) ** inner_n)) * ith_bound
    if rttvars[-1] > rttvar_delta:
        print("Problem with bound on last rttvar.")
    g_values.append(rttvar_delta)
    

# Create the scatter plot
ax3.scatter(x, y, label="Samples $S_i, S_{i+1}, ..., S_{i+n}$", alpha=0.8, color='tan')

# Plot functions
ax3.plot(x, f(x, c+r))
ax3.plot(x, f(x, c-r))
ax3.plot(x, rtos, label='RTO')
ax3.plot(x, srtts, label='SRTT', alpha=0.5)

ax4.plot(x, rttvars, label='RTTVar', color='red')
ax4.plot(x[1:], g_values, label='$\\Delta$', color='purple')


ax3.spines.bottom.set_visible(False)
ax4.spines.top.set_visible(False)
ax3.xaxis.tick_top()
ax3.tick_params(labeltop=False)  # don't put tick labels at the top
ax4.xaxis.tick_bottom()

# legend1 = ax1.legend(loc="upper right", edgecolor="black")
# legend2 = ax2.legend(loc="upper right", edgecolor="black")
# legend1.get_frame().set_alpha(None)
# legend2.get_frame().set_alpha(None)
# legend1.get_frame().set_facecolor((1, 1, 1, 1))
# legend2.get_frame().set_facecolor((1, 1, 1, 1))

# Set axis labels and title
plt.xlabel('Number N of consecutive c/r steady-state samples')
# plt.ylabel('ms')

d = .5  # proportion of vertical to horizontal extent of the slanted line
kwargs = dict(marker=[(-1, -d), (1, d)], markersize=12,
              linestyle="none", color='k', mec='k', mew=1, clip_on=False)
ax3.plot([0, 1], [0, 0], transform=ax3.transAxes, **kwargs)
ax4.plot([0, 1], [1, 1], transform=ax4.transAxes, **kwargs)

legend1 = ax1.legend(loc="upper right", edgecolor="black")
legend2 = ax2.legend(loc="upper right", edgecolor="black", bbox_to_anchor=(1.0, 1.2))
legend1.get_frame().set_alpha(None)
legend2.get_frame().set_alpha(None)
legend1.get_frame().set_facecolor((1, 1, 1, 1))
legend2.get_frame().set_facecolor((1, 1, 1, 1))


plt.show()
