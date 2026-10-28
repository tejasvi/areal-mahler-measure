# Flammang's table

`table2/` holds two transcriptions of Table 2 of Flammang's paper: one from the HAL version's text layer
(`flammang2015_table2_pdftotext_79c01c8c.json`, made by `parse_table2_67d9bc59.py`) and one from images of its pages
(`flammang2015_table2_image_transcription_8720412f.json`). They agree except for row 58, to which the text layer appends
fragments of the page footer; the image transcription has the printed row. `repro_table2_19cdc09e.py` evaluates her
auxiliary function with the printed weights and re-optimizes the weights. With the image transcription, the printed weights
give `N₀ ≥ 1.3800359` and the re-optimized weights give `N₀ ≥ 1.3800500`. Its outputs for both transcriptions are the two
`.out` files. Most of the search used the text transcription (`search/data/A58.json`); the last linear program and the
export of the lower certificate used the image transcription (`search/data/A58v.json`).
