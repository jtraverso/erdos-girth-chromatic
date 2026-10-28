# Graphs of large girth and large chromatic number in Lean 4: Erdős, Mycielski, Larsen–Propp–Ullman

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Three classical results on graphs with large chromatic number. Mathlib has girth
(`SimpleGraph.egirth`) and chromatic number but none of these theorems, and no fractional chromatic
number.

**Erdős (1959)**, namespace `ErdosGirthChromatic` (version 1, unchanged):

1. `exists_girth_indep` (**structural form**). For every `g` and every `ε > 0`, for all
   sufficiently large `n`, there is a graph on `n` vertices with no cycle of length at most `g` in
   which every independent set has fewer than `εn` vertices.
2. `exists_girth_not_colorable`. For every `g` and `k`, for all sufficiently large `n`, there is
   a graph on `n` vertices with girth greater than `g` that is not `k`-colourable.
3. `exists_girth_chromaticNumber` (**Erdős' theorem**). There is a finite graph with girth
   greater than `g` and chromatic number greater than `k`.

**Mycielski (1955)**, namespace `Mycielski` (version 2). `M(G)` has an original and a shadow copy of
each vertex and an apex adjacent to the shadows; the other edges follow `G`.

4. `card_vertex`: `M(G)` has `2|V| + 1` vertices.
5. `graph_cliqueFree_three_iff`: `M(G)` is triangle-free iff `G` is.
6. `colorable_succ_iff`: `M(G)` is `(k+1)`-colourable iff `G` is `k`-colourable.
7. `chromaticNumber_graph`: `χ(M(G)) = χ(G) + 1` for every finite `G`.
8. `card_familyVertex`, `family_cliqueFree_three`, `family_chromaticNumber`: iterating from `K₂`
   gives triangle-free graphs with `3·2ⁿ − 1` vertices and chromatic number `n + 2`.
9. `exists_triangleFree_chromaticNumber_ge`: triangle-free graphs of unbounded chromatic number.

**Larsen–Propp–Ullman (1995)**, namespace `FractionalColouring` (version 2). A fractional colouring
puts nonnegative weights on vertex sets, zero off the independent sets, covering every vertex with
total weight at least `1`; `χ_f(G)` is the infimum of the total weights (`fracChromaticNumber`).

10. `fracChromaticNumber_mycielski`: `χ_f(M(G)) = χ_f(G) + 1/χ_f(G)` for every finite graph `G` with
    at least one vertex. So along the Mycielski family `χ` grows by one per step while `χ_f`
    follows `a ↦ a + 1/a`.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean), [`GirthLib/`](GirthLib) (Erdős), [`Mycielski/`](Mycielski)
  (Mycielski) and [`FractionalLib/`](FractionalLib) (fractional colourings, LP duality,
  Larsen–Propp–Ullman): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof of Erdős' theorem goes

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

## How the proof of Larsen–Propp–Ullman goes

1. **Duality.** A fractional clique gives every independent set weight at most `1`. Weak duality:
   its total weight is at most that of any fractional colouring. Strong duality (finite LP duality,
   `FractionalLib/FiniteLPDuality.lean`): some fractional clique weighs exactly `χ_f(G)`.
2. **Upper bound.** From a fractional colouring `x` of `G` of weight `t ≥ 1`, give `I ∪ I'` weight
   `(t−1)/t · x(I)`, `I ∪ {w}` weight `x(I)/t`, and the shadow layer weight `1/t`. This colours
   `M(G)` with total weight `t + 1/t`; letting `t` tend to `χ_f(G)` gives `≤`.
3. **Lower bound.** From an optimal fractional clique `g` of `G`, `a = χ_f(G)`, put `(1 − 1/a)g` on the
   originals, `g/a` on the shadows and `1/a` on the apex (total `a + 1/a`). For an independent set
   with originals `J` and shadows `K` and no apex, `g(K \ J) ≤ (1 − g(J)) a` by weak duality on
   `G` minus the closed neighbourhood of `J`, so the set has weight at most `1`.

## Sources

* P. Erdős, *Graph theory and probability*, Canad. J. Math. 11 (1959) 34–38,
  doi:10.4153/CJM-1959-003-9.
* J. Mycielski, *Sur le coloriage des graphs*, Colloq. Math. 3 (1955) 161–162,
  doi:10.4064/cm-3-2-161-162. (The existence corollary from Mycielski's construction is also
  registered by another author: PALOMAR-2026-10-14-000006.)
* M. Larsen, J. Propp, D. Ullman, *The fractional chromatic number of Mycielski's graphs*,
  J. Graph Theory 19 (1995) 411–416, doi:10.1002/jgt.3190190313.

## Authorship and use of AI

The author chose the results. Version 1 (Erdős): the statements and proof plan were written with
Claude in Claude Code, and Harmonic's Aristotle produced the proofs, which were audited and rebuilt
locally. Version 2: the Mycielski library was written with OpenAI Codex (repository
`jtraverso/mycielski`, merged unchanged); the fractional colouring library and the
Larsen–Propp–Ullman proof were written with Claude in Claude Code, reusing the author's finite LP
duality module from the Lean development of Erdős #81 Paper I. Lean checks everything mechanically.
See `formalization.yaml`.

## Versions

* Version 1 (PALOMAR-2026-10-17-000009): Erdős' theorem.
* Version 2: adds Mycielski's construction and the Larsen–Propp–Ullman theorem; the version 1
  statements are unchanged.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
