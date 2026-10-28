# Lean proofs

The Lean files (Lean version v4.35.0-rc3, Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e, as in
`lean/lake-manifest.json`) are laid out as follows; `lean/SHA256SUMS` lists every file in `lean/`.

- `lean/Areal/`: the statements (`Statement.lean`); the proofs of Pritsker's formula, of Lemmas 2.1 and 3.1 and of
  Corollary 2.2; the correctness proofs of the checking programs (`Areal/Cert/` for the lower certificate, `Areal/UCert/`
  for the upper certificate); and the four theorems (`LowerN.lean`, `LowerK.lean`, `UpperN.lean`, `UpperK.lean`).
- `lean/AuxCommon/`: general lemmas (energy smoothing, integrality, potentials of measures).
- `lean/ArealCore/`, `lean/ArealUCore/`, `lean/AuxCore/`: the checking programs, in exact integer arithmetic, with the
  certificate data and the coverings.
- `lean/ArealN/`, `lean/ArealUN/`: the checks evaluated by `native_decide`; `lean/ArealK/`, `lean/ArealUK/`: the checks
  evaluated by the kernel.
- `lean/data/`: copies of the lower certificate, of the upper certificate and of its form used by the Lean proofs, and
  auxiliary data (root brackets, coverings, energy blocks) that the checks verify.
- `lean/tools/`: the programs that generated Lean files from the certificates (see the Notes).
- `lean/Bench/`: the files that print the axioms, and helper programs.

The top-level README states the four theorems `Areal.areal_lower_N`, `Areal.areal_lower_K`, `Areal.areal_upper_N` and
`Areal.areal_upper_K`, and gives the build commands and the axioms that they print.

In the kernel, the build of `Areal.LowerK` checks 12,101 intervals and windows and 1,747 parts of the energy, and the
build of `Areal.UpperK` checks 33,326 intervals and 146 root windows in 16,736 shards of two leaves, together with 147
root brackets and 4 pairs of complex conjugate roots; for each interval the pass over the 12,670 nodes of the density is
split into four kernel-checked parts, and each root window is checked whole.

| build | resources |
|---|---|
| `Areal.LowerK` | about 210 CPU-hours; six machines with 60 to 88 threads each did it in about 50 minutes |
| `Areal.UpperK` | about 1,000 CPU-hours |
| `Areal.UpperN` | about 26 minutes with 44 threads |

From the shipped files, the following commands regenerate the generated modules of the kernel-only upper proof
(`ArealUCore/Lits.lean`, the generated files in `ArealUK/`, `Areal/UCert/LeavesKG/` and `Areal/UCert/LeavesK.lean`) and
`data/c2parts_U5b.txt`. They overwrite these files, so run them in a copy of `lean/` and compare the result with
`lean/SHA256SUMS`. The middle command takes about two hours as one process; its range of leaves can be split into parts
whose outputs are concatenated in order.

    bash tools/genK_U5b.sh
    lake build arlseg && ./.lake/build/bin/arlseg 3168 0 33472 > SEGS.txt
    python3 -I tools/genKsplit_U5b.py 3168 SEGS.txt

Further checks. All four theorems were rebuilt on another machine, and

- the exported proofs of `areal_lower_N` and `areal_upper_N`, with their auxiliary axioms admitted, were accepted by
  `leanchecker` and by two further implementations of the Lean kernel, nanoda and lean4lean;
- `areal_lower_K` was rebuilt from scratch and re-checked by Lean's kernel module by module, and its complete exported
  proof was accepted by nanoda;
- `areal_upper_K` was rebuilt from scratch and re-checked by Lean's kernel module by module; `leanchecker`, nanoda and
  lean4lean accepted a sample of 107 generated modules, and `leanchecker` and lean4lean accepted the final assembly of
  the proof, in which the theorems of the generated modules, and three general lemmas used to assemble them, are taken as
  axioms.

In each of the four proofs, the corresponding check fails if an end point of the first group of intervals is moved, or if
the constant that the check claims there is raised by the smallest margin in that group; that constant is `m` in the two
lower proofs and the lower bound 0 for the function of (C3) in the two upper proofs.
