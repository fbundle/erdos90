# Source: https://arxiv.org/src/2605.20695

## Note on LaTeX Source

The arXiv source endpoint (https://arxiv.org/src/2605.20695) returned a binary gzip archive (application/gzip, approximately 38.1KB). The raw binary content cannot be rendered as text. To access the actual LaTeX source:

1. Download directly: `curl -L https://arxiv.org/src/2605.20695 -o remarks_2605_20695_src.tar.gz`
2. Extract: `tar -xzf remarks_2605_20695_src.tar.gz`

The source archive is expected to contain:
- Main `.tex` file with the full paper (38KB is larger, suggesting multiple contributor sections or detailed proofs)
- Any `.bib` bibliography files

## Paper Identification

- arXiv ID: 2605.20695
- Title: Remarks on the disproof of the unit distance conjecture
- Authors: Noga Alon, Thomas F. Bloom, W. T. Gowers, Daniel Litt, Will Sawin, Arul Shankar, Jacob Tsimerman, Victor Wang, Melanie Matchett Wood
- Submitted: 20 May 2026
- License: CC BY 4.0

## Key Mathematical Content (from HTML rendering)

See `remarks_2605_20695_html_full.md` for the complete mathematical content extracted from the HTML-rendered version, including:
- Main Theorem 1.1 statement
- Lemma 2.1 (Geometry of Numbers) with proof
- Lemma 2.2 (Counting Magnitude-1 Elements) with proof
- Full proof of Theorem 1.1 with explicit example (T = {3,5,7,11,13,17}, S = {101,∞})
- Explicit exponent: approximately 1 + 6.24·10⁻³⁸
- All 9 author reflections (Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang, Wood)
- Complete bibliography (37 entries)

## Structure of Source (Expected)

Based on the HTML rendering, the LaTeX source likely contains:
- Introduction with historical context
- Section 2 with Lemmas 2.1 and 2.2 and their proofs
- Sections 3-11 with individual reflections from each author
- Acknowledgements
- Bibliography with 37 entries including Erdős, Spencer-Szemerédi-Trotter, Golod-Shafarevich, Ellenberg-Venkatesh, Guth-Katz, Hajir-Maire-Ramakrishna
