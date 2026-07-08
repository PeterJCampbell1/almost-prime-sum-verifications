# Explicit almost-prime verification scripts

This repository contains Python scripts used to verify finite numerical computations appearing in an explicit almost-prime paper.

The scripts are intended to be readable and reproducible. They use only the Python standard library.

## Current scripts

### `verify_K_presieved.py`

Verifies the finite computations in Lemma K-presieved. The script checks the three numerical bounds used in the proof:

1. Case 1: the large-\(w\) bound is less than `1.0651`;
2. Case 2: the finite maximum for \(2 \leq w < 286\), \(z \geq 286\), is less than `1.1282`;
3. Case 3: the finite supremum for \(z_0 \leq z < 286\) is less than `1.1458`.

Together these imply the lemma with constant

\[
K = 1.146.
\]

## Running the scripts

From the repository directory, run:

```bash
python3 verify_K_presieved.py
