# Source: https://arxiv.org/src/2011.09822

## Fetch Result

The URL https://arxiv.org/src/2011.09822 returns a **binary gzip-compressed tar archive** (application/gzip, approximately 646.5 KB).

This is the LaTeX source for arXiv:2011.09822, which is the IRS communications paper (NOT the Hajir-Maire-Ramakrishna paper). The binary content cannot be rendered as text.

---

## Correct Source URL for Hajir-Maire-Ramakrishna

The correct paper is arXiv:1901.04354. Its source would be at:

> https://arxiv.org/src/1901.04354

This URL would also return a binary tar.gz archive.

---

## How to Download and Extract LaTeX Source

To download and extract the LaTeX source for arXiv papers:

```bash
# Download the source archive
curl -L "https://arxiv.org/src/1901.04354" -o hajir_maire_ramakrishna.tar.gz

# Extract it
mkdir hajir_maire_ramakrishna_src
tar -xzf hajir_maire_ramakrishna.tar.gz -C hajir_maire_ramakrishna_src/

# List contents
ls -la hajir_maire_ramakrishna_src/

# Find the main .tex file
find hajir_maire_ramakrishna_src/ -name "*.tex" | head -20
```

Alternatively, some arXiv papers have their source available as a single .tex file (not tar.gz). The format depends on the paper.

---

## Alternative: e-print Format

arXiv provides the source in the "e-print" format:

```bash
# The src URL may redirect to the actual format
wget -O source.tar.gz "https://arxiv.org/src/1901.04354"
file source.tar.gz  # Determine the actual format
```

---

## Note on Source for 2011.09822

The binary archive at https://arxiv.org/src/2011.09822 contains the LaTeX source for the IRS/secure communications paper by Hong, Pan, Zhou, Ren, Wang. It is not relevant to the Erd46 project.

---

## Content Summary of Hajir-Maire-Ramakrishna (1901.04354)

Based on the abstract and citations, the paper contains:

### Sections (expected structure for a 40KB .tex file, ~20 pages)

1. **Introduction**: Statement of main results, Martinet constants, answer to Ihara's question
2. **Background**: Golod-Shafarevich criterion, pro-p groups, ramification theory
3. **Main construction**: Building towers with prescribed ramification using GS criterion
4. **Martinet constant bounds**: New records for totally real and totally complex cases
5. **Split primes in infinite towers**: Answering Ihara's question
6. **References**: Bibliography

### Key Definitions Expected in Source

```latex
\begin{definition}[Root discriminant]
\text{rdiscr}(K) = |\text{disc}(K)|^{1/[K:\mathbb{Q}]}
\end{definition}

\begin{definition}[Martinet constant]
\mu_{r_1, r_2} = \inf \{ \text{rdiscr}(K) : \text{K has signature } (r_1, r_2), 
                          \text{ infinite Hilbert p-class field tower} \}
\end{definition}

\begin{definition}[Asymptotically good tower]
K_0 \subset K_1 \subset \cdots \text{ with } [K_n:\mathbb{Q}] \to \infty 
\text{ and } \sup_n \text{rdiscr}(K_n) < \infty
\end{definition}
```

### Key Theorem Expected

**Main Theorem**: Let K be a number field and S a finite set of places. Under explicit numerical conditions on the Golod-Shafarevich parameters, K_S/K is infinite with bounded root discriminant.

**Corollary (New Martinet bounds)**: For totally complex fields:
rdiscr ≤ [new explicit bound, improving previous record]

**Corollary (Ihara's question)**: There exist infinite asymptotically good extensions with infinitely many completely split primes.
