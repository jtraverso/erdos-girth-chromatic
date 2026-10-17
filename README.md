# Erdős' theorem on graphs of large girth and large chromatic number in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

**Erdős (1959).** For every `g` and `k` there is a finite graph with girth greater than `g` and
chromatic number greater than `k`. Mathlib has girth (`SimpleGraph.egirth`) and chromatic number
but not this theorem.

All statements are in the namespace `ErdosGirthChromatic`:

1. `exists_girth_indep` (**structural form**). For every `g` and every `ε > 0`, for all
   sufficiently large `n`, there is a graph on `n` vertices with no cycle of length at most `g` in
   which every independent set has fewer than `εn` vertices.
2. `exists_girth_not_colorable`. For every `g` and `k`, for all sufficiently large `n`, there is
   a graph on `n` vertices with girth greater than `g` that is not `k`-colourable.
3. `exists_girth_chromaticNumber` (**Erdős' theorem**). There is a finite graph with girth
   greater than `g` and chromatic number greater than `k`.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`GirthLib/`](GirthLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

The proof is Erdős's probabilistic method. It is written with explicit finite weighted sums
rather than a measure-theoretic random graph.

1. **Weights.** A graph on `m` vertices with edge set `S` gets weight
   `p^{|S|} (1 − p)^{(m choose 2) − |S|}`. These weights sum to `1`.
2. **Short cycles.** A fixed cycle of length `ℓ` has weight `p^ℓ`, and there are at most `m^ℓ`
   closed walks of length `ℓ`. So the expected number of cycles of length at most `g` is at most
   `∑_{ℓ ≤ g} (mp)^ℓ`.
3. **Independent sets.** The expected number of independent `t`-sets is
   `(m choose t) (1 − p)^{(t choose 2)}`.
4. **Parameters.** With `m = 2n`, `p = q^{−(2g+1)}` and `t = q^{2g+2}`, where `q^{2g+3} ≈ 2n`,
   both expectations are small. So some graph has fewer than `n` short cycles and no independent
   `t`-set.
5. **Deletion.** Delete one vertex from each short cycle and take the graph induced on `n` of the
   remaining vertices. It has girth greater than `g`, and all its independent sets have fewer
   than `t ≤ εn` vertices.
6. **Colouring.** A `k`-colouring would have a colour class of size at least `n/k`, which is too
   large for an independent set.

## Sources

* P. Erdős, *Graph theory and probability*, Canad. J. Math. 11 (1959) 34–38,
  doi:10.4153/CJM-1959-003-9.

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
