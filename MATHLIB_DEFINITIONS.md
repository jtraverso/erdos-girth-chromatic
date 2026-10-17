# Mathlib definitions used in Challenge.lean (Erdős 1959, girth and chromatic number)

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
