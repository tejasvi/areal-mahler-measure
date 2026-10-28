# Earlier versions and provenance of the files

The runs in `audit/` outside `audit/L3/` and `audit/U5/` are for certificates of earlier versions of the paper:

| certificate | bound | used in | runs in `audit/` |
|---|---|---|---|
| `cert_arllo_L1_4c5758a0.json` (preliminary run's lower certificate) | 1.3823468 | version 1 (from the preliminary run) | `audit/controls/lower_hidden/` and the files of `audit/logs/` with `L1` in their names |
| `cert_arlup_U2_cb2c7960.json` | 1.3842933 | versions 1 to 3 | the other runs outside `audit/U3/` and `audit/U4/` |
| `cert_arlup_U3_40f09d6b.json` | 1.3841169 | version 4 | `audit/U3/` |
| `cert_arlup_U4_82d31e67.json` | 1.3840959 | version 5 | `audit/U4/` |

These four are archived with the earlier versions (doi:10.5281/zenodo.23532710, doi:10.5281/zenodo.23541254,
doi:10.5281/zenodo.23547620 and doi:10.5281/zenodo.23550271) and are not included here; the export commands at the end of
`search/COMMANDS.txt` reproduce all four. Versions 5 to 8 also contained Lean proofs, assuming Smith's theorem, of the
bound 1.3840959 of version 5; they are archived with those versions.

`arl_upper.py` made the upper certificate of versions 1 to 3 of the paper, and `arl_upper5.py` and `arl_upper6.py` made
those of versions 4 and 5; `arl_upper4.py` to `arl_upper7.py` are later versions, whose headers describe each change.
The solutions and logs in `search/lp/` include those of a first attempt with the refined nodes, whose certificate the
checker rejected.

Versions 1 and 2 of the paper stated that two independent transcriptions of Flammang's table agree. They differ in the
last row: the transcription from the text layer ends with `1001x² − 80x + 3` instead of the printed `591x² − 36x + 1`,
which the transcription from page images has (checked against the published PDF). Neither certificate contains this row,
so no bound changes.

## Provenance of the files

The checkers, the certificates, the logs and the control files are unchanged since the audit. The `.lean` files differ
  from the audited ones only in comments, and the generators in `lean/tools/` only in their comments and in the comment
  text that they write into the files they generate. The copies of the search programs, of
  `controls/*/make_dip_arl_*.py` and of `logs/lower/diag_L3.py` use paths relative to the program's directory, and
  `tp_primal_hat.py`, which `tp_upper_lp.py` imports, is copied from the release of the upper-bound companion paper
  (doi:10.5281/zenodo.23529778). Some of the programs that generated Lean files are not included, because they contain a
  path of the machine on which they ran or read files from outside `lean/`; the files they generated are included, and
  Lean checks them like all other files.

## Older names and formats

Some names in the checkers, certificates and logs predate the paper: Lemma 2.1 of the paper is called "Lemma TA1" there
and Lemma 3.1 "Lemma UA1"; the lemmas of the companion papers from which they are adapted are called "Lemma TP1" (for
the lower bound) and "Lemma U1" (for the upper bound). The conditions (C1)–(C3) are "(U1)–(U3)", and the bound on
`(1/s) ∫ g dμ` is "(V)".

`certificate/formats/` holds the format `tpmahler-cert-v1` of the lower-bound companion paper (doi:10.5281/zenodo.23524856)
and the format `tpmahler-upper-v1` of the upper-bound companion paper (doi:10.5281/zenodo.23529776). The formats of L3 and
U5, `tpmahler-areal-lower-v1` and `tpmahler-areal-upper-v1`, have exactly their fields. Only the left side of `F` changes,
from `log⁺x` to `g(x)`, and the claim of U5 bounds `(1/s) ∫ g dμ` instead of `(1/s) ∫ log⁺x dμ`.

