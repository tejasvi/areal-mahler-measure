# Bounds for the smallest limit point of the areal Mahler measure of totally positive algebraic integers

This repository holds the certificates, checking programs and Lean proofs for the paper *Bounds for the smallest limit
point of the areal Mahler measure of totally positive algebraic integers* by Tejasvi Singh Tomar
([doi:10.5281/zenodo.23715993](https://doi.org/10.5281/zenodo.23715993)), and it is archived in the supplement record
[doi:10.5281/zenodo.23715998](https://doi.org/10.5281/zenodo.23715998). The certificates and proofs establish the bounds

    1.3830134 < e^m ≤ E_A⁺ ≤ λ_A⁺ ≤ e^v < 1.3839579

of Theorem 1.1 of the paper, where `λ_A⁺` is the smallest limit point and `E_A⁺` the essential minimum of the areal
Mahler measure `N₀` on totally positive algebraic integers, `m` is the constant of the lower certificate L3 and `v` the
bound of the upper certificate U5:

    m = 45636208945290293391/140737488355328000000,   e^m = 1.38301343…
    v = 64989486877/200000000000,                     e^v = 1.38395789…

The upper bound uses a theorem of Smith (his Theorem 1.5 for intervals, in the form quoted in Section 5 of the paper);
the two Lean proofs of the upper bound take it as the hypothesis `SmithThm15`.

## Checking the certificates

### Running the checkers

Requirements: Python 3 (we used 3.12.13) with python-flint (0.9.0). Both checkers refuse to run under `python -O`. The last
argument is the number of processes.

    python3 -I checker/lower/check_arl_lo_59a1c54c.py certificate/lower/cert_arllo_L3_5295faaa.json 48   # 3,665 s
    python3 -I checker/upper/check_arl_up_a17af685.py certificate/upper/cert_arlup_U5_d445679c.json 48   # 453 s

Each checker prints its intermediate results and ends with `VERIFIED` and exit status 0 only if every condition holds.
The times are those of our runs, each on a server with 96 threads; the logs are `logs/lower/check_arllo_L3_5295faaa.log`
and `logs/upper/check_arlup_U5_d445679c.log`.

| certificate | lemma of the paper | polynomials | nodes of `G` | interval | interval checks |
|---|---|---|---|---|---|
| L3 | 2.1 | 34 | 4,660 | `[0, 24]` | 69,298 |
| U5 | 3.1 | 33 | 12,670 | `[237/1600, 20]` | 70,829 (for (C3)) |

Here `G` is the piecewise linear function of L3 and the piecewise linear density of U5.

About 43,000 of the interval checks for L3 fall on the single interval `[24, 4357]`, and one process does all of them,
so more processes do not make the lower check much faster.

### What the checkers verify

The lower checker shows that the function `F` of L3 is positive on `(0, ∞)` outside the roots of its polynomials, and the
upper checker shows (C1)–(C3) and the bound on `(1/s) ∫ g dμ` for U5. For the methods, see Section 4 of the paper and the
docstrings of the checkers.

All polynomials in both certificates appear in Flammang's Table 2, and the certificates list their coefficients, so the
checks do not depend on a transcription of the table. The fields of L3 and U5 are those of the formats in
`certificate/formats/`, with `g` in place of `log⁺`. These formats are described in `HISTORY.md`, together with the older
names that the output and the certificates use, such as Lemma TA1 and Lemma UA1 for Lemmas 2.1 and 3.1.

### Second checker and controls

A second checker, `audit/check_arl_second.py`, was written from the certificate formats and the lemmas of the paper
without reference to the checkers in `checker/`. It bounds the same functions from below by quadratic minorants from
Taylor's formula, as explained in its docstring. In our runs, shown below with their numbers of processes and times, it also ends with `VERIFIED` on both certificates.
These runs and further ones are listed in `audit/L3/RUNS.md` and `audit/U5/RUNS.md`:

    python3 -I audit/check_arl_second.py certificate/lower/cert_arllo_L3_5295faaa.json 48   # 612 s
    python3 -I audit/check_arl_second.py certificate/upper/cert_arlup_U5_d445679c.json 24   # 95 s

`controls/lower/summary.txt` and `controls/upper/summary.txt` list the 34 modified certificates in `controls/` (16 for L3,
18 for U5) with their verdicts. All the checkers reject them except two that still state true bounds:

- `neg_m_plus_2e-6.json` raises `m` by 2·10^-6, less than the margin of 3·10^-6 that the search left;
- `neg_POSITIVE_v_plus_1e-6.json` raises `v` by 10^-6, which only weakens the claim.

They also reject four further narrow notches and bumps in `audit/L3/controls/` and `audit/U5/controls/`.

## Lean proofs

`lean/` contains Lean 4 proofs of four theorems (Lean v4.35.0-rc3, Mathlib commit
c55e6e786f49471c72fbddbec5415808896aec1e). Their claims are stated in `lean/Areal/Statement.lean`:

    theorem areal_lower_N : LowerClaim ∧ LowerDecClaim ∧ LimitLowerClaim
    theorem areal_lower_K : LowerClaim ∧ LowerDecClaim ∧ LimitLowerClaim
    theorem areal_upper_N (hS : SmithThm15) : UpperClaim ∧ LimitUpperClaim
    theorem areal_upper_K (hS : SmithThm15) : UpperClaim ∧ LimitUpperClaim

    def LowerClaim : Prop := ∀ ε : ℝ, 0 < ε → (ArLow (m0 - ε)).Finite
    def LowerDecClaim : Prop :=
      {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧ N0 P ≤ 13830134 / 10000000}.Finite
    def LimitLowerClaim : Prop := ∀ y : ℝ, AccPt y (𝓟 LAplus) → Real.exp m0 ≤ y
    def UpperClaim : Prop :=
      {α : ℂ | IsIntegral ℤ α ∧ ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧ N0 P < 13839579 / 10000000}.Infinite
    def LimitUpperClaim : Prop := ∃ y : ℝ, AccPt y (𝓟 LAplus) ∧ y ≤ Real.exp vstar

`LowerDecClaim` is part (i) of Theorem 1.1 and `UpperClaim` is part (ii); `LowerClaim` gives `e^m ≤ E_A⁺`,
`LimitLowerClaim` gives `e^m ≤ λ_A⁺` and `LimitUpperClaim` gives `λ_A⁺ ≤ e^v`. Like part (i), `LowerClaim` and
`LowerDecClaim` concern all totally positive algebraic numbers. The theorems are in the namespace `Areal`, `m0` and
`vstar` are `m` and `v`, `N0` is defined from Pritsker's integral, and `SmithThm15` is the hypothesis above.

The two upper theorems use U5b (`lean/data/cert_arlup_U5b_cff7f76e.json`), the certificate U5 with its 10 weights below
10^-7 set to 0 (23 polynomials). In the `_N` theorems the certificate checks are evaluated as compiled code
(`native_decide`), and in the `_K` theorems the Lean kernel evaluates them. With a Mathlib cache:

    cd lean
    lake exe cache get
    lake build Areal.LowerN
    lake build Areal.LowerK    # about 210 CPU-hours
    lake build Areal.UpperN    # about 26 minutes with 44 threads
    lake build Areal.UpperK    # about 1,000 CPU-hours
    lake env lean Bench/AxLowerN.lean    # propext, Classical.choice, Quot.sound and 85 axioms of compiled checks
    lake env lean Bench/AxLowerK.lean    # propext, Classical.choice, Quot.sound
    lake env lean Bench/AxUpperN.lean    # propext, Classical.choice, Quot.sound and 45 axioms of compiled checks
    lake env lean Bench/AxUpperK.lean    # propext, Classical.choice, Quot.sound

`LEAN.md` describes the layout of `lean/`, the resources the builds use, how to regenerate
the generated modules, and further checks on the four proofs.

## Other files

| path | content |
|---|---|
| `checker/*/diff_*.txt` | the differences between these checkers and the companion papers' checkers they were derived from |
| `logs/` | also the certificate summaries by row number of Flammang's table, `COMMANDS.txt` and a run-time diagnostic |
| `search/` | the floating-point search that produced the certificates (see `search/README.md`) |
| `table2/` | two transcriptions of Flammang's Table 2 (see `table2/README.md`) |
| `smyth/` | the values of `N₀(β_n²)` along Smyth's sequence |
| `paper/` | the LaTeX source of the paper |
| `HISTORY.md` | earlier certificates and versions, older names, and the provenance of the files |

## Licence

Apache-2.0 for the programs (see `LICENSE`); the certificates, data and logs are released under CC BY 4.0 with the paper.
