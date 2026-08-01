# Verification scripts for explicit almost-prime computations

This repository contains the Python scripts used to verify the finite
numerical computations in an explicit almost-prime paper.

The scripts are intended to be readable and reproducible. They require
Python 3 and use only the Python standard library.

## Scripts

### `verify_K_presieved.py`

Verifies the finite computations used to establish the dimension
condition after pre-sieving by \(3\). In particular, it checks the
numerical bounds arising in the five cases of the proof of the
dimension-condition lemma and confirms the constants

\[
K=1.146
\]

for \(z\geq z_0\), and

\[
K=1.097
\]

for \(z\geq 10^8\).

The corresponding output is recorded in:

```text
output_K_presieved.txt
```

### `verify_V_presieved_lower_bound.py`

Computes the finite prime product used in the lower bound for the
main-term factor \(V(z)\). It verifies the numerical computation leading
to

\[
V(z)\geq \frac{1.241}{\log^2 z}
\qquad (z\geq 10^8).
\]

The corresponding output is recorded in:

```text
output_V_presieved_lower_bound.txt
```

### `verify_case2_presieved.py`

Performs the finite verification for the intermediate range

\[
z_0<z\leq 10^8.
\]

The script constructs a finite covering by intervals and verifies, on
each interval, that the lower bound for the sifted sum is positive for
at least one value of

\[
\delta\in\{0.20,0.60,0.75,0.85,0.93\}.
\]

A logarithmic safety margin of \(0.10\) is used when selecting interval
endpoints, so the accepted inequalities do not depend on subtracting
nearly equal floating-point quantities.

The corresponding output is recorded in:

```text
output_case2_presieved.txt
```

## Running the scripts

From the repository directory, run:

```bash
python3 verify_K_presieved.py
python3 verify_V_presieved_lower_bound.py
python3 verify_case2_presieved.py
```

On systems where Python 3 is invoked using `python`, replace `python3`
with `python`.

The included output files were generated from the corresponding scripts.
