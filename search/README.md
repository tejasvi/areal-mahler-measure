# Search

The programs in `search/` are not needed to check the certificates. For the lower bound, `arl_nodes.py` chooses the
nodes from the solution of a preliminary run with the nodes `k/100` of `[0, 20]`, `arl_primal.py` minimizes `∫ g dθ`
over measures with piecewise linear densities on these nodes subject to `∫ log|Q| dθ ≥ 0` for the polynomials of
Flammang's Table 2 and to a nonnegative logarithmic energy, `arl_dual.py` solves the linear program for the auxiliary
function with this measure as the reference measure, and `export_arl_lo.py` writes the exact certificate. For the upper
bound, `arl_upper.py` solves the linear program for the measure and the weights by cutting planes, and
`export_arl_up.py` writes the exact certificate. `arl_upper7.py`, which also adds all nodes and their midpoints to the
check grid, made the certificate in `certificate/upper/`. Like `arl_upper5.py` and `arl_upper6.py`, it solves each
linear program by the interior-point method of cvxopt. `adapt_nodes_up.py` refines the nodes where the density of the
version-5 solution has an edge or a large jump. `search/COMMANDS.txt` gives the command lines, and the solutions and
logs of the runs are in `search/lp/`. The export commands at the end of `search/COMMANDS.txt` reproduce both
certificates, the lower certificate of version 1 (from the preliminary run) and the three earlier upper certificates
byte for byte from the stored solutions; see `search/REPRO_EXPORT.txt`. The search also needs numpy, scipy, cvxpy, clarabel and cvxopt.

The nodes of the lower certificate come from a preliminary run of the two steps with the nodes `k/100` on `[0, 20]`: to the
points `k/100` of `[0, 24]` were added the points at distance `k/2000`, `0 ≤ k ≤ 8`, from each of the 189 positive roots of
the polynomials that received weight more than `10^-6` in its linear program, rounded to ten decimal places, and nodes were
then removed until consecutive nodes were at least `2·10^-4` apart. The linear program of the lower bound imposes the
inequality on `F` on about `4.7·10^5` points of `(0, 80]`, which include many points near the roots of the `Q_j`, and adds
cutting planes at the local minima of `F`. For the upper bound the nodes have spacing `1/400`, refined to `1/800` and
`1/1600` where the density found by the previous search has an edge or a large jump. The constraints were
`Σ b_j deg Q_j ≤ 1 − 10^-6`, `∫ log|Q_j| dμ ≥ 2·10^-6`, and `U − Σ b_j log|Q_j| ≥ 3·10^-6` on a grid; cutting planes refine
the grid until this function is positive on a check grid of spacing `2·10^-5` near the support of the density, to which all
nodes and midpoints of the nodes are added.
`search/screens/` holds the screens of further polynomials mentioned in Section 6 of the paper, a test of resultant
constraints on the measure of the lower bound (`resultant_pilot.py`) and the runs on the effect of the spacing and of
the interval, with their logs (see `search/COMMANDS.txt`).
