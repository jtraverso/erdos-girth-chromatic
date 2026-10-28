# Mathlib definitions used in Challenge.lean (Erdős 1959, Mycielski 1955, Larsen–Propp–Ullman 1995)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.Walk.IsCycle

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 84:

```lean
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup
```

## SimpleGraph.egirth

`Mathlib/Combinatorics/SimpleGraph/Girth.lean`, line 31:

```lean
/--
The extended girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is
acyclic.
-/
noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length
```

## SimpleGraph.IsIndepSet

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 907:

```lean
/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
@[wikidata Q1060343]
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)
```

## SimpleGraph.Coloring

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 74:

```lean
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α
```

## SimpleGraph.Hom

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 293:

```lean
/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
```

## RelHom

`Mathlib/Order/RelIso/Basic.lean`, line 46:

```lean
/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
structure RelHom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α → β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : ∀ {a b}, r a b → s (toFun a) (toFun b)
```

## SimpleGraph.Colorable

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 163:

```lean
/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))
```

## SimpleGraph.chromaticNumber

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 212:

```lean
/-- The chromatic number of a graph is the minimal number of colors needed to color it.
This is `⊤` (infinity) iff `G` isn't colorable with finitely many colors.

If `G` is colorable, then `ENat.toNat G.chromaticNumber` is the `ℕ`-valued chromatic number. -/
noncomputable def chromaticNumber : ℕ∞ := ⨅ n ∈ Set.ofPred G.Colorable, (n : ℕ∞)
```

## Complete graph

[Mathlib/Combinatorics/SimpleGraph/Basic.lean:330](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L330)

```lean
/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices. -/
@[wikidata Q45715]
abbrev completeGraph (V : Type u) : SimpleGraph V := ⊤
```

## Adjacency in the complete graph

[Mathlib/Combinatorics/SimpleGraph/Basic.lean:337](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L337)

```lean
@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl
```

## Clique

[Mathlib/Combinatorics/SimpleGraph/Clique.lean:47](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Clique.lean#L47)

```lean
/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
```

## Clique of prescribed order

[Mathlib/Combinatorics/SimpleGraph/Clique.lean:245](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Clique.lean#L245)

```lean
/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n
```

## Clique-freeness

[Mathlib/Combinatorics/SimpleGraph/Clique.lean:378](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Clique.lean#L378)

```lean
/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t
```

## Fintype cardinality

[Mathlib/Data/Fintype/Card.lean:39](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Fintype/Card.lean#L39)

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```

## Finset.filter

`Mathlib/Data/Finset/Filter.lean`, lines 46–53:

```lean
variable (p : α → Prop) [DecidablePred p] {s t : Finset α}

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
```

## Finset.sum

`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`, lines 68–69 (`Finset.sum` is the additive
version of `Finset.prod`, generated by `to_additive`; `∑ x, f x` is `∑ x ∈ Finset.univ, f x`):

```lean
protected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=
  (s.1.map f).prod
```

## Infimum of a set of reals

`Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`, lines 115–116 and 127–128:

```lean
noncomputable instance : SupSet ℝ :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

noncomputable instance : InfSet ℝ :=
  ⟨fun s => -sSup (-s)⟩
```

