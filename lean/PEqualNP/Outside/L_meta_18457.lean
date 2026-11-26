import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18457
namespace L_meta_6500

open scoped BigOperators

noncomputable section

def pop {α : Type*} (p : α → Prop) : ℕ :=
  Nat.card {a : α // p a}

theorem pop_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    pop p = (Finset.univ.filter p).card := by
  rw [pop, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem pop_congr {α β : Type*}
    (e : α ≃ β) (p : α → Prop) (q : β → Prop)
    (h : ∀ a, p a ↔ q (e a)) : pop p = pop q :=
  Nat.card_congr (e.subtypeEquiv h)

theorem pop_prod {α β : Type*} [Fintype α] [Finite β] (p : α → β → Prop) :
    pop (fun z : α × β => p z.1 z.2) = ∑ a : α, pop (p a) := by
  simp only [pop, ← Nat.card_sigma]
  let e : {z : α × β // p z.1 z.2} ≃ Σ a : α, {b : β // p a b} :=
    ⟨fun x => ⟨x.val.1,x.val.2,x.property⟩,
      fun x => ⟨(x.1,x.2.val),x.2.property⟩, fun _ => rfl, fun _ => rfl⟩
  exact Nat.card_congr e

theorem pop_pi {ι β : Type*} [Finite ι] (p : β → Prop) :
    pop (fun f : ι → β => ∀ i, p (f i)) = pop p ^ Nat.card ι :=
  (Nat.card_congr Equiv.subtypePiEquivPi).trans Nat.card_fun

theorem pop_not {α : Type*} [Fintype α] (p : α → Prop) :
    pop (fun x => ¬ p x) = Nat.card α - pop p := by
  classical
  have he : (Finset.univ.filter fun x => ¬ p x) = (Finset.univ.filter p)ᶜ := by
    ext x
    simp
  rw [pop_filter, pop_filter, he, Finset.card_compl, Nat.card_eq_fintype_card]

theorem pop_if {α : Type*} [Fintype α] (h : Prop) [Decidable h] (p : α → Prop) :
    pop (fun x => h ∧ p x) = if h then pop p else 0 := by
  classical
  rw [pop_filter, pop_filter]
  by_cases hh : h <;> simp [hh]

theorem pop_gt {K : ℕ} (a : Fin K) : pop (fun x => a < x) = K - 1 - a.val := by
  rw [pop_filter]
  have e : Finset.univ.filter (fun x => a < x) = Finset.Ioi a := by
    ext x
    simp
  rw [e, Fin.card_Ioi]

abbrev Leaf (K : ℕ) := Fin K × (Fin 2 → Fin K)
abbrev Branch (K : ℕ) := Fin K × (Fin 2 → Leaf K)
abbrev Pattern (K : ℕ) := Fin K × (Fin 3 → Branch K)

def localMin {K : ℕ} (r : Fin K) (l : Leaf K) : Prop :=
  l.1 < r ∧ ∀ i, l.1 < l.2 i

def blocked {K : ℕ} (r : Fin K) (b : Branch K) : Prop :=
  b.1 ≤ r ∧ ∀ i, ¬ localMin b.1 (b.2 i)

def qualifies {K : ℕ} (x : Pattern K) : Prop :=
  ∀ i, ¬ blocked x.1 (x.2 i)

theorem card_leaf (K : ℕ) : Nat.card (Leaf K) = K ^ 3 := by
  simp only [Leaf, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  rw [show (3 : ℕ) = 1 + 2 by rfl, pow_add, pow_one]

theorem card_branch (K : ℕ) : Nat.card (Branch K) = K ^ 7 := by
  change Nat.card (Fin K × (Fin 2 → Leaf K)) = _
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fun, Nat.card_fin, card_leaf, ← pow_mul]
  rw [show (7 : ℕ) = 1 + 3 * 2 by rfl, pow_add, pow_one]

theorem card_pattern (K : ℕ) : Nat.card (Pattern K) = K ^ 22 := by
  change Nat.card (Fin K × (Fin 3 → Branch K)) = _
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fun, Nat.card_fin, card_branch, ← pow_mul]
  rw [show (22 : ℕ) = 1 + 7 * 3 by rfl, pow_add, pow_one]

def prefixLeaf (K k : ℕ) : ℕ := ∑ t ∈ Finset.range k, (K - 1 - t) ^ 2

def prefixBranch (K k : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (k + 1), (K ^ 3 - prefixLeaf K t) ^ 2

theorem pop_localMin {K : ℕ} (r : Fin K) :
    pop (localMin r) = prefixLeaf K r.val := by
  change pop (fun z : Fin K × (Fin 2 → Fin K) => z.1 < r ∧ ∀ i, z.1 < z.2 i) = _
  rw [pop_prod (fun (a : Fin K) (b : Fin 2 → Fin K) => a < r ∧ ∀ i, a < b i)]
  simp_rw [pop_if, pop_pi, Nat.card_fin, pop_gt]
  change (∑ x : Fin K, if x.val < r.val then (K - 1 - x.val) ^ 2 else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun t => if t < r.val then (K - 1 - t) ^ 2 else 0) K,
    prefixLeaf]
  have vanish (i : ℕ) (_ : i ∈ Finset.range K) (h : i ∉ Finset.range r.val) :
      (if i < r.val then (K - 1 - i) ^ 2 else 0) = 0 := by
    have him : ¬ i < r.val := fun hi => h (Finset.mem_range.mpr hi)
    simp [him]
  refine (Finset.sum_subset (Finset.range_mono r.isLt.le) vanish).symm.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem pop_blocked {K : ℕ} (r : Fin K) :
    pop (blocked r) = prefixBranch K r.val := by
  change pop (fun z : Fin K × (Fin 2 → Leaf K) => z.1 ≤ r ∧ ∀ i, ¬ localMin z.1 (z.2 i)) = _
  rw [pop_prod (fun (a : Fin K) (b : Fin 2 → Leaf K) => a ≤ r ∧ ∀ i, ¬ localMin a (b i))]
  have eq (a : Fin K) :
      pop (fun b : Fin 2 → Leaf K => a ≤ r ∧ ∀ i, ¬ localMin a (b i)) =
        if a ≤ r then (K ^ 3 - prefixLeaf K a.val) ^ 2 else 0 := by
    rw [pop_if (a ≤ r) (fun b : Fin 2 → Leaf K => ∀ i, ¬ localMin a (b i)),
      pop_pi (ι := Fin 2) (fun l : Leaf K => ¬ localMin a l), Nat.card_fin,
      pop_not (localMin a), card_leaf, pop_localMin]
  simp only [eq]
  change (∑ x : Fin K, if x.val ≤ r.val then (K ^ 3 - prefixLeaf K x.val) ^ 2 else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun t => if t ≤ r.val then (K ^ 3 - prefixLeaf K t) ^ 2 else 0) K,
    prefixBranch]
  have vanish (i : ℕ) (_ : i ∈ Finset.range K) (h : i ∉ Finset.range (r.val + 1)) :
      (if i ≤ r.val then (K ^ 3 - prefixLeaf K i) ^ 2 else 0) = 0 := by
    have hh : ¬ i ≤ r.val := fun hi => h (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    simp [hh]
  refine (Finset.sum_subset (Finset.range_mono r.isLt) vanish).symm.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  have hh : i ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp [hh]

theorem pop_qualifies (K : ℕ) :
    pop (@qualifies K) = ∑ k ∈ Finset.range K, (K ^ 7 - prefixBranch K k) ^ 3 := by
  change pop (fun x : Fin K × (Fin 3 → Branch K) => ∀ i, ¬ blocked x.1 (x.2 i)) = _
  rw [pop_prod (fun (a : Fin K) (b : Fin 3 → Branch K) => ∀ i, ¬ blocked a (b i))]
  have eq (a : Fin K) :
      pop (fun b : Fin 3 → Branch K => ∀ i, ¬ blocked a (b i)) =
        (K ^ 7 - prefixBranch K a.val) ^ 3 := by
    rw [pop_pi (ι := Fin 3) (fun b : Branch K => ¬ blocked a b), Nat.card_fin,
      pop_not (blocked a), card_branch, pop_blocked]
  simp only [eq]
  exact Fin.sum_univ_eq_sum_range (fun t => (K ^ 7 - prefixBranch K t) ^ 3) K

def tallies (K : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | k + 1 =>
    let old := tallies K k
    let branch := old.2.1 + (K ^ 3 - old.1) ^ 2
    (old.1 + (K - 1 - k) ^ 2, branch, old.2.2 + (K ^ 7 - branch) ^ 3)

theorem tallies_spec (K k : ℕ) :
    (tallies K k).1 = prefixLeaf K k ∧
    (tallies K k).2.1 = ∑ t ∈ Finset.range k, (K ^ 3 - prefixLeaf K t) ^ 2 ∧
    (tallies K k).2.2 = ∑ t ∈ Finset.range k, (K ^ 7 - prefixBranch K t) ^ 3 := by
  induction k with
  | zero => simp [tallies, prefixLeaf]
  | succ k ih =>
    rcases ih with ⟨ha,hb,ht⟩
    simp only [tallies, Finset.sum_range_succ, ha, hb, ht]
    constructor
    · simp only [prefixLeaf, Finset.sum_range_succ]
    · constructor
      · trivial
      · rw [show prefixBranch K k =
            (∑ t ∈ Finset.range k, (K ^ 3 - prefixLeaf K t) ^ 2) +
              (K ^ 3 - prefixLeaf K k) ^ 2 by rw [prefixBranch, Finset.sum_range_succ]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem finite_rank_count :
    5 * Nat.card (Pattern 512) ≤ 14 * pop (@qualifies 512) := by
  rw [card_pattern, pop_qualifies, ← (tallies_spec 512 512).2.2]
  decide

end

end L_meta_6500


namespace L_meta_6500

open SimpleGraph

noncomputable section

inductive Position
  | root
  | child (i : Fin 3)
  | grand (i : Fin 3) (j : Fin 2)
  | leaf (i : Fin 3) (j k : Fin 2)
  deriving DecidableEq

private def other {V : Type*} (G : SimpleGraph V) (u v : V) : Set V :=
  G.neighborSet u \ {v}

structure LocalTree {V : Type*} (G : SimpleGraph V) (v : V) where
  first : Fin 3 ≃ G.neighborSet v
  second (i : Fin 3) : Fin 2 ≃ other G (first i).val v
  third (i : Fin 3) (j : Fin 2) : Fin 2 ≃ other G (second i j).val (first i).val

private def enumerate {α : Type*} [Finite α] {m : ℕ} (h : Nat.card α = m) : Fin m ≃ α := by
  letI := Fintype.ofFinite α
  exact (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans h)).symm

private def next {V : Type*} [Finite V] (G : SimpleGraph V) {u v : V}
    (hv : G.Adj u v) (hd : (G.neighborSet u).ncard = 3) : Fin 2 ≃ other G u v :=
  enumerate (by
    rw [Nat.card_coe_set_eq, other, Set.ncard_sdiff_singleton_of_mem hv, hd])

def LocalTree.build {V : Type*} [Finite V] (G : SimpleGraph V) (B : Set V) {v : V}
    (closed : ∀ u ∈ B, ∀ w, G.Adj u w → w ∈ B)
    (deg : ∀ u ∈ B, (G.neighborSet u).ncard = 3) (hv : v ∈ B) : LocalTree G v := by
  let a : Fin 3 ≃ G.neighborSet v := enumerate ((Nat.card_coe_set_eq _).trans (deg v hv))
  have ha (i : Fin 3) : (a i).val ∈ B := closed v hv _ (a i).property
  let b (i : Fin 3) : Fin 2 ≃ other G (a i).val v :=
    next G (show G.Adj v (a i).val from (a i).property).symm (deg _ (ha i))
  have hb (i : Fin 3) (j : Fin 2) : (b i j).val ∈ B :=
    closed _ (ha i) _ (b i j).property.1
  exact ⟨a,b,fun i j => next G (show G.Adj (a i).val (b i j).val from (b i j).property.1).symm (deg _ (hb i j))⟩

namespace LocalTree

variable {V : Type*} {G : SimpleGraph V} {v : V}

def a (T : LocalTree G v) (i : Fin 3) : V := (T.first i).val
def b (T : LocalTree G v) (i : Fin 3) (j : Fin 2) : V := (T.second i j).val
def c (T : LocalTree G v) (i : Fin 3) (j k : Fin 2) : V := (T.third i j k).val

theorem va (T : LocalTree G v) (i : Fin 3) : G.Adj v (T.a i) := (T.first i).property
theorem ab (T : LocalTree G v) (i : Fin 3) (j : Fin 2) : G.Adj (T.a i) (T.b i j) :=
  (T.second i j).property.1
theorem bc (T : LocalTree G v) (i : Fin 3) (j k : Fin 2) : G.Adj (T.b i j) (T.c i j k) :=
  (T.third i j k).property.1
theorem bv (T : LocalTree G v) (i : Fin 3) (j : Fin 2) : T.b i j ≠ v :=
  (T.second i j).property.2
theorem ca (T : LocalTree G v) (i : Fin 3) (j k : Fin 2) : T.c i j k ≠ T.a i :=
  (T.third i j k).property.2

def point (T : LocalTree G v) : Position → V
  | .root => v
  | .child i => T.a i
  | .grand i j => T.b i j
  | .leaf i j k => T.c i j k

def walk (T : LocalTree G v) : (p : Position) → G.Walk v (T.point p)
  | .root => .nil
  | .child i => .cons (T.va i) .nil
  | .grand i j => .cons (T.va i) (.cons (T.ab i j) .nil)
  | .leaf i j k => .cons (T.va i) (.cons (T.ab i j) (.cons (T.bc i j k) .nil))

theorem cv (T : LocalTree G v) (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length)
    (i : Fin 3) (j k : Fin 2) : T.c i j k ≠ v := by
  intro equality
  have bv := T.bv i j
  have av := (T.va i).ne
  have ab := (T.ab i j).ne
  have endAdj : G.Adj (T.b i j) v := (congrArg (G.Adj (T.b i j)) equality).mp (T.bc i j k)
  let p : G.Walk (T.a i) v := .cons (T.ab i j) (.cons endAdj .nil)
  have path : p.IsPath := by
    simp [p, Walk.isPath_def, bv, av.symm, ab]
  have edge : s(v,T.a i) ∉ p.edges := by
    simp [p, bv.symm, av, ab]
  have impossible := girth v (.cons (T.va i) p) ((Walk.cons_isCycle_iff p (T.va i)).mpr ⟨path,edge⟩)
  change (7 : ℕ) ≤ 3 at impossible
  omega

theorem walk_path (T : LocalTree G v)
    (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length) (p : Position) :
    (T.walk p).IsPath := by
  apply (Walk.isPath_def _).mpr
  cases p with
  | root =>
    change ([v] : List V).Nodup
    simp
  | child i =>
    change ([v,T.a i] : List V).Nodup
    simp [(T.va i).ne]
  | grand i j =>
    change ([v,T.a i,T.b i j] : List V).Nodup
    simp [(T.va i).ne, (T.bv i j).symm, (T.ab i j).ne]
  | leaf i j k =>
    change ([v,T.a i,T.b i j,T.c i j k] : List V).Nodup
    simp [(T.va i).ne, (T.bv i j).symm, (T.ab i j).ne,
      (T.cv girth i j k).symm, (T.ca i j k).symm, (T.bc i j k).ne]

theorem support_list (T : LocalTree G v) (p : Position) :
    (T.walk p).support = match p with
    | .root => [v]
    | .child i => [v,T.a i]
    | .grand i j => [v,T.a i,T.b i j]
    | .leaf i j k => [v,T.a i,T.b i j,T.c i j k] := by
  cases p <;> rfl

theorem walk_short (T : LocalTree G v) (p : Position) : (T.walk p).length ≤ 3 := by
  cases p with
  | root => exact (by decide : (0 : ℕ) ≤ 3)
  | child => exact (by decide : (1 : ℕ) ≤ 3)
  | grand => exact (by decide : (2 : ℕ) ≤ 3)
  | leaf => exact (by decide : (3 : ℕ) ≤ 3)

private theorem equal_support {u w : V} (p : G.Walk v u) (q : G.Walk v w)
    (ep : u = w) (hp : p.IsPath) (hq : q.IsPath)
    (lp : p.length ≤ 3) (lq : q.length ≤ 3)
    (girth : ∀ u (r : G.Walk u u), r.IsCycle → 7 ≤ r.length) : p.support = q.support := by
  subst w
  have equal : p = q := by
    by_contra h
    obtain ⟨x,_,_,r,hr,hr'⟩ := hp.exists_isCycle_length_le_add_of_ne hq h
    have := girth x r hr
    omega
  exact congrArg Walk.support equal

theorem point_injective (T : LocalTree G v)
    (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length) :
    Function.Injective T.point := by
  intro p q e
  have supports := equal_support (T.walk p) (T.walk q) e (T.walk_path girth p)
    (T.walk_path girth q) (T.walk_short p) (T.walk_short q) girth
  rw [T.support_list p, T.support_list q] at supports
  cases p <;> cases q <;> simp at supports ⊢
  case child.child i i' =>
    exact T.first.injective (Subtype.ext supports)
  case grand.grand i j i' j' =>
    obtain ⟨a,b⟩ := supports
    have e : i = i' := T.first.injective (Subtype.ext a)
    subst i'
    exact ⟨rfl, (T.second i).injective (Subtype.ext b)⟩
  case leaf.leaf i j k i' j' k' =>
    obtain ⟨a,b,c⟩ := supports
    have e : i = i' := T.first.injective (Subtype.ext a)
    subst i'
    have e : j = j' := (T.second i).injective (Subtype.ext b)
    subst j'
    exact ⟨rfl, rfl, (T.third i j).injective (Subtype.ext c)⟩

end LocalTree

def select {V : Type*} {K : ℕ} (G : SimpleGraph V) (r : V → Fin K) (v : V) : Prop :=
  ∀ u, G.Adj v u → r u ≤ r v →
    ∃ p, G.Adj u p ∧ p ≠ v ∧ ∀ q, G.Adj p q → r p < r q

theorem selected_independent {V : Type*} {K : ℕ} (G : SimpleGraph V) (r : V → Fin K)
    {u v : V} (hu : select G r u) (hv : select G r v) : ¬ G.Adj u v := by
  intro e
  have impossible {x y : V} (hx : select G r x) (hy : select G r y) (e : G.Adj x y)
      (h : r x ≤ r y) : False := by
    obtain ⟨p,xp,_,low⟩ := hy x e.symm h
    obtain ⟨q,pq,_,lower⟩ := hx p xp (le_of_lt (low x xp.symm))
    exact (lt_asymm (low q pq)) (lower p pq.symm)
  exact (le_total (r u) (r v)).elim (impossible hu hv e) (impossible hv hu e.symm)

end

end L_meta_6500
namespace L_meta_6500

open SimpleGraph

noncomputable section

def pattern (K : ℕ) : (Position → Fin K) ≃ Pattern K where
  toFun f :=
    (f .root, fun i =>
      (f (.child i), fun j => (f (.grand i j), fun k => f (.leaf i j k))))
  invFun p
    | .root => p.1
    | .child i => (p.2 i).1
    | .grand i j => ((p.2 i).2 j).1
    | .leaf i j k => ((p.2 i).2 j).2 k
  left_inv f := by funext x; cases x <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; rfl

theorem LocalTree.select_iff {V : Type*} {G : SimpleGraph V} {v : V}
    (T : LocalTree G v) {K : ℕ} (r : V → Fin K) :
    select G r v ↔ qualifies (pattern K (r ∘ T.point)) := by
  classical
  change select G r v ↔ ∀ i : Fin 3, ¬ (r (T.a i) ≤ r v ∧ ∀ j : Fin 2,
    ¬ (r (T.b i j) < r (T.a i) ∧ ∀ k : Fin 2, r (T.b i j) < r (T.c i j k)))
  constructor
  · intro picked i bad
    obtain ⟨p, edge, avoids, low⟩ := picked (T.a i) (T.va i) bad.1
    let p' : other G (T.a i) v := ⟨p,edge,avoids⟩
    let j := (T.second i).symm p'
    have eq : T.b i j = p := congrArg Subtype.val ((T.second i).apply_symm_apply p')
    apply bad.2 j
    refine ⟨?_, ?_⟩
    · simpa only [eq] using low (T.a i) edge.symm
    · intro k
      have nextEdge : G.Adj p (T.c i j k) := by
        simpa only [eq] using T.bc i j k
      simpa only [eq] using low (T.c i j k) nextEdge
  · intro good u uv bound
    let u' : G.neighborSet v := ⟨u,uv⟩
    let i := T.first.symm u'
    have eq : T.a i = u := congrArg Subtype.val (T.first.apply_symm_apply u')
    have hr : r (T.a i) ≤ r v := by simpa only [eq] using bound
    have notAll : ¬ ∀ j : Fin 2, ¬ (r (T.b i j) < r (T.a i) ∧
        ∀ k : Fin 2, r (T.b i j) < r (T.c i j k)) := fun no => good i ⟨hr,no⟩
    obtain ⟨j, yes⟩ := Classical.not_forall.mp notAll
    have low := Classical.not_not.mp yes
    refine ⟨T.b i j, ?_, T.bv i j, ?_⟩
    · simpa only [eq] using T.ab i j
    · intro q qp
      by_cases e : q = T.a i
      · simpa only [e] using low.1
      · let q' : other G (T.b i j) (T.a i) := ⟨q,qp,e⟩
        let k := (T.third i j).symm q'
        have eq' : T.c i j k = q := congrArg Subtype.val ((T.third i j).apply_symm_apply q')
        simpa only [eq'] using low.2 k

end

end L_meta_6500


namespace L_meta_6500.Averaging

open scoped BigOperators

noncomputable def partition {P V : Type*} (pos : P ↪ V) :
    (P ⊕ {v : V // v ∉ Set.range pos}) ≃ V := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective pos pos.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun v => v ∈ Set.range pos))

noncomputable def factor {P V R : Type*} (pos : P ↪ V) :
    (V → R) ≃ (P → R) × ({v : V // v ∉ Set.range pos} → R) :=
  ((partition pos).symm.arrowCongr (Equiv.refl R)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem factor_fst {P V R : Type*} (pos : P ↪ V) (r : V → R) :
    (factor pos r).1 = r ∘ pos := by
  funext x
  rfl

def subtypePair {A B : Type*} (p : A → Prop) :
    {z : A × B // p z.1} ≃ {z : A // p z} × B where
  toFun z := (⟨z.1.1,z.2⟩,z.1.2)
  invFun z := ⟨(z.1.1,z.2),z.1.2⟩
  left_inv := by rintro ⟨⟨a,b⟩,h⟩; rfl
  right_inv := by rintro ⟨⟨a,h⟩,b⟩; rfl

theorem restriction_count {P V R : Type*} (pos : P ↪ V) (p : (P → R) → Prop) :
    Nat.card {r : V → R // p (r ∘ pos)} =
      Nat.card {r : P → R // p r} * Nat.card ({v : V // v ∉ Set.range pos} → R) := by
  let e : {r : V → R // p (r ∘ pos)} ≃
      {z : (P → R) × ({v : V // v ∉ Set.range pos} → R) // p z.1} :=
    Equiv.subtypeEquiv (factor pos) (fun r => by rw [factor_fst pos r])
  rw [Nat.card_congr (e.trans (subtypePair p)), Nat.card_prod]

theorem restriction_bound {P V R : Type*} (pos : P ↪ V) (p : (P → R) → Prop)
    (a b : Nat) (h : a * Nat.card (P → R) ≤ b * Nat.card {r : P → R // p r}) :
    a * Nat.card (V → R) ≤ b * Nat.card {r : V → R // p (r ∘ pos)} := by
  rw [restriction_count pos p, Nat.card_congr (factor (R := R) pos), Nat.card_prod]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right
    (Nat.card ({v : V // v ∉ Set.range pos} → R)) h

theorem local_to_global {P V R T : Type*} (pos : P ↪ V) (pattern : (P → R) ≃ T)
    (qualifies : T → Prop) (select : (V → R) → Prop) (a b : Nat)
    (hLocal : a * Nat.card T ≤ b * Nat.card {t : T // qualifies t})
    (hSelect : ∀ r, select r ↔ qualifies (pattern (r ∘ pos))) :
    a * Nat.card (V → R) ≤ b * Nat.card {r : V → R // select r} := by
  have h := restriction_bound pos (fun r => qualifies (pattern r)) a b (by
    rw [Nat.card_congr pattern, Nat.card_congr (Equiv.subtypeEquivOfSubtype pattern)]
    exact hLocal)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hSelect)]
  exact h

theorem witness {V R : Type*} [Fintype R] [Nonempty R] (B : Finset V)
    (select : R → V → Prop) [∀ r v, Decidable (select r v)] (a b : Nat)
    (h : ∀ v ∈ B, a * Nat.card R ≤ b * Nat.card {r : R // select r v}) :
    ∃ r : R, a * B.card ≤ b * (B.filter (select r)).card := by
  classical
  let U : Finset R := Finset.univ
  have hc (v : V) : Nat.card {r : R // select r v} = (U.filter fun r => select r v).card := by
    calc
      _ = Nat.card ↥(U.filter fun r => select r v) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun r => by simp [U]))
      _ = _ := by
        let S := U.filter (fun r => select r v)
        letI : Fintype ↥S := Fintype.ofFinset (p := {r | r ∈ S}) S (fun _ => Iff.rfl)
        exact Nat.card_eq_fintype_card.trans (Fintype.card_ofFinset S (fun _ => Iff.rfl))
  have hsum : (∑ r ∈ U, (B.filter (select r)).card) =
      ∑ v ∈ B, (U.filter fun r => select r v).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlo : a * Nat.card R * B.card ≤ b * ∑ r ∈ U, (B.filter (select r)).card := by
    calc
      _ = ∑ v ∈ B, a * Nat.card R := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ B, b * (U.filter fun r => select r v).card :=
        Finset.sum_le_sum (fun v hv => by simpa only [hc] using h v hv)
      _ = _ := by rw [hsum, Finset.mul_sum]
  by_contra no
  have hlt (r : R) : b * (B.filter (select r)).card < a * B.card :=
    Nat.lt_of_not_ge (fun h => no ⟨r,h⟩)
  have hs : (∑ r ∈ U, b * (B.filter (select r)).card) <
      ∑ r ∈ U, a * B.card :=
    Finset.sum_lt_sum (fun r _ => le_of_lt (hlt r))
      ⟨Classical.choice inferInstance, Finset.mem_univ _, hlt _⟩
  rw [← Finset.mul_sum] at hs
  have rhs : (∑ r ∈ U, a * B.card) = a * Nat.card R * B.card := by
    simp [U, Nat.card_eq_fintype_card, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact (not_lt_of_ge hlo) (hs.trans_le (le_of_eq rhs))

end L_meta_6500.Averaging
theorem L_meta_6500 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), (∀ x4 ∈ x3, ∀ (x6 : Fin x1), x2.Adj x4 x6 → x6 ∈ x3) → (∀ x5 ∈ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → ∃ x7 ⊆ x3, (∀ x8 ∈ x7, ∀ x10 ∈ x7, ¬x2.Adj x8 x10) ∧ (5 : ℕ) * x3.card ≤ (14 : ℕ) * x7.card := by
  classical
  intro n G B closed degree girth
  open L_meta_6500 in
  have perVertex (v : Fin n) (hv : v ∈ B) :
      5 * Nat.card (Fin n → Fin 512) ≤ 14 * Nat.card {r : Fin n → Fin 512 // select G r v} := by
    let T : LocalTree G v := LocalTree.build G (B : Set (Fin n)) closed degree hv
    let pos : Position ↪ Fin n := ⟨T.point, T.point_injective girth⟩
    exact Averaging.local_to_global pos (pattern 512) qualifies (fun r => select G r v)
      5 14 finite_rank_count (fun r => T.select_iff r)
  open L_meta_6500 in
  obtain ⟨r, hr⟩ := Averaging.witness B (select G) 5 14 perVertex
  let I := B.filter (L_meta_6500.select G r)
  refine ⟨I, Finset.filter_subset _ _, ?_, hr⟩
  intro u hu v hv
  exact L_meta_6500.selected_independent G r
    (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2

namespace L_meta_6502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def rho (n d i : ℕ) : ℕ := if i < n + d then i else i - 1

def fx (n d L j i : ℕ) : ℕ := if i < n + j then rho n d i else n + L

def ng (n : ℕ) (gs : List Gate) (d : ℕ) : List Gate :=
  List.ofFn fun k : Fin (gs.length - 1) =>
    let j := if k.val < d then k.val else k.val + 1
    let h := gs.getD j ⟨GateOp.or, []⟩
    ⟨h.op, h.inputs.map (fx n d gs.length j)⟩

theorem ng_len (n : ℕ) (gs : List Gate) (d : ℕ) : (ng n gs d).length = gs.length - 1 := by
  simp [ng]

theorem sem (n : ℕ) (gs : List Gate) (d : ℕ) (hd : d < gs.length)
    (hno : ∀ (j : ℕ) (hj : j < gs.length), d < j → n + d ∉ gs[j].inputs)
    (x : List Bool) (hx : x.length = n) :
    ∀ w, w < n + gs.length → w ≠ n + d →
      (run (ng n gs d) x).getD (rho n d w) false = (run gs x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwd
    by_cases h9 : w < n
    · rw [rho, if_pos (by omega), run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      have old := run_gate gs x j hj
      rw [hx] at old
      rw [old]
      obtain ⟨k, hkj, hkL, hr⟩ : ∃ k, (if k < d then k else k + 1) = j ∧
          k < gs.length - 1 ∧ rho n d (n + j) = n + k := by
        by_cases h : j < d
        · exact ⟨j, by rw [if_pos h], by omega, by unfold rho; split_ifs <;> omega⟩
        · exact ⟨j - 1, by rw [if_neg (by omega)]; omega, by omega, by
            unfold rho; split_ifs <;> omega⟩
      have new := run_gate (ng n gs d) x k (by rw [ng_len]; omega)
      rw [hx] at new
      have e : (ng n gs d)[k]'(by rw [ng_len]; omega) =
          ⟨gs[j].op, gs[j].inputs.map (fx n d gs.length j)⟩ := by
        have hgd : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := List.getD_eq_getElem _ _ hj
        simp only [ng, List.getElem_ofFn, hkj, hgd]
      rw [hr, new, e, List.map_map]
      refine congrArg _ (List.map_congr_left fun i hi => ?_)
      simp only [Function.comp]
      by_cases hij : i < n + j
      · have hne : i ≠ n + d := by
          rintro rfl
          exact hno j hj (by omega) hi
        have hlt : rho n d i < n + k := by
          by_cases hkd : k < d
          · rw [if_pos hkd] at hkj
            unfold rho; split_ifs <;> omega
          · rw [if_neg hkd] at hkj
            unfold rho; split_ifs <;> omega
        have hfx : fx n d gs.length j i = rho n d i := if_pos hij
        rw [hfx, if_pos hlt, if_pos hij]
        exact ih i hij (by omega) hne
      · have hfx : fx n d gs.length j i = n + gs.length := if_neg hij
        rw [hfx, if_neg hij, if_neg (by omega)]

theorem del (n : ℕ) (C : Circuit) (hC : FanInTwo C) (d : ℕ) (hd : d < C.gates.length)
    (hno : ∀ (j : ℕ) (hj : j < C.gates.length), d < j → n + d ∉ C.gates[j].inputs)
    (ho : C.output ≠ n + d) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧ circuitFun n D = circuitFun n C := by
  let o := if C.output < n + C.gates.length then rho n d C.output else n + C.gates.length
  refine ⟨⟨ng n C.gates d, o⟩, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hh
    have hj : (if k.val < d then k.val else k.val + 1) < C.gates.length := by
      have := k.isLt
      split_ifs <;> omega
    dsimp only
    rw [List.getD_eq_getElem _ _ hj]
    have := hC _ (List.getElem_mem hj)
    exact ⟨this.1, by simpa using this.2⟩
  · change (ng n C.gates d).length + 1 = C.gates.length
    rw [ng_len]; omega
  · funext x
    change (run (ng n C.gates d) (List.ofFn x)).getD o false =
      (run C.gates (List.ofFn x)).getD C.output false
    by_cases h : C.output < n + C.gates.length
    · simp only [o, if_pos h]
      exact sem n _ d hd hno _ (by simp) _ h ho
    · simp only [o, if_neg h]
      rw [List.getD_eq_default _ _ (by rw [run_length, ng_len, List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]





def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi


def fn (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def X0 (u t : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t)

def X1 (u t v : Fin 9) : Fin 9 → Bool := fun i => decide (i = u) || decide (i = t) || decide (i = v)

/-- `not` gates read one wire -/
def nrm (g : Gate) : Gate := ⟨g.op, rds g⟩

theorem nrm_run (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (x : List Bool) :
    run (gs.map nrm) x = run gs x := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc,
      ih fun g' h => hop g' (by simp [h])]
    congr 2
    rcases hop g (by simp) with h | h | h
    · simp [nrm, rds, h]
    · simp [nrm, rds, h]
    · rcases g with ⟨o, l⟩
      simp only at h
      subst h
      rcases l with _ | ⟨a, l⟩ <;> simp [nrm, rds, GateOp.eval]


theorem cnt (n m o : ℕ) (R : ℕ → List ℕ) (hR : ∀ k, (R k).length ≤ 2)
    (Hu : ∀ k < m, n + k = o ∨ ∃ j, k + 1 ≤ j ∧ j < m ∧ n + k ∈ R j) :
    ∀ r k (U : List ℕ), k + r = m → U.Nodup →
      (∀ i ∈ U, i < n + k ∧ (i = o ∨ ∃ j, k ≤ j ∧ j < m ∧ i ∈ R j)) → U.length ≤ r + 1 := by
  classical
  intro r
  induction r with
  | zero =>
    intro k U hk hnd hU
    have all : ∀ i ∈ U, i = o := by
      intro i hi
      rcases (hU i hi).2 with h | ⟨j, h1, h2, _⟩
      · exact h
      · omega
    rcases U with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp
    · simp
    · exfalso
      have e1 := all a (by simp)
      have e2 := all b (by simp)
      rw [e1, e2] at hnd
      simp at hnd
  | succ r ih =>
    intro k U hk hnd hU
    have hkm : k < m := by omega
    have h1 : (U.filter (· ∈ R k)).length ≤ 2 := by
      have hs : (U.filter (· ∈ R k)).Subperm (R k) :=
        List.subperm_of_subset (hnd.filter _) fun x hx => by simpa using (List.mem_filter.1 hx).2
      exact hs.length_le.trans (hR k)
    have h2 := List.length_eq_length_filter_add (l := U) (fun x => decide (x ∈ R k))
    have h3 := ih (k + 1) ((n + k) :: U.filter (fun x => !decide (x ∈ R k))) (by omega) (by
      rw [List.nodup_cons]
      refine ⟨fun h => ?_, hnd.filter _⟩
      have := (hU _ (List.mem_of_mem_filter h)).1
      omega) (by
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact ⟨by omega, Hu k hkm⟩
      · obtain ⟨h4, h5⟩ := List.mem_filter.1 hi
        obtain ⟨h6, h7⟩ := hU i h4
        refine ⟨by omega, ?_⟩
        rcases h7 with h7 | ⟨j, h7, h8, h9⟩
        · exact Or.inl h7
        · right
          refine ⟨j, ?_, h8, h9⟩
          rcases Nat.lt_or_ge k j with h | h
          · omega
          · have : j = k := by omega
            rw [this] at h9
            simp [h9] at h5)
    rw [List.length_cons] at h3
    omega

theorem cntp {α : Type} (p : α → Bool) : ∀ l : List α, l.countP p = (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card
  | [] => by simp
  | a :: l => by
    have ih := cntp p l
    have e : (Finset.univ.filter fun i : Fin (a :: l).length => p ((a :: l).get i) = true).card =
        (if p a = true then 1 else 0) + (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card := by
      have := Fin.card_filter_univ_succ (n := l.length) (fun i : Fin (l.length + 1) => p ((a :: l).get i) = true)
      rw [show (Finset.univ.filter fun i : Fin (a :: l).length => p ((a :: l).get i) = true).card = (Finset.univ.filter fun i : Fin (l.length + 1) => p ((a :: l).get i) = true).card from rfl, this]
      by_cases h : p a = true
      · simp [h, Function.comp_def, add_comm]
      · simp [h, Function.comp_def]
    rw [e, ← ih, List.countP_cons, add_comm]





theorem fcount (eff : Gate → List ℕ) (v : ℕ) : ∀ gs : List Gate, (gs.filter fun g => (eff g).contains v).length ≤ (gs.flatMap eff).count v
  | [] => by simp
  | g :: gs => by
    have ih := fcount eff v gs
    rw [List.flatMap_cons, List.count_append, List.filter_cons]
    split_ifs with h
    · have : 0 < (eff g).count v := List.count_pos_iff.2 (by simpa using h)
      simp only [List.length_cons]
      omega
    · omega

theorem flen (eff : Gate → List ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, (eff g).length ≤ bif g.op.eval [false] then 1 else 2) →
    (gs.flatMap eff).length + (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    have ih := flen eff gs fun g' h' => h g' (List.mem_cons_of_mem _ h')
    have h1 := h g List.mem_cons_self
    rw [List.flatMap_cons, List.length_append, List.filter_cons, List.length_cons]
    cases hb : g.op.eval [false] with
    | true =>
      rw [hb] at h1
      simp only [if_true, List.length_cons, cond_true] at h1 ⊢
      omega
    | false =>
      rw [hb] at h1
      simp only [cond_false] at h1
      rw [if_neg (by simp)]
      omega

theorem csum (l : List ℕ) (S : Finset ℕ) : ∑ w ∈ S, l.count w ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    have : ∑ w ∈ S, (if (a == w) = true then 1 else 0) ≤ 1 := by
      simp only [beq_iff_eq, Finset.sum_ite_eq]
      split_ifs <;> omega
    omega

theorem aux : True := trivial

end L_meta_6502

theorem L_meta_6502 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 →     (∀ (x4 : Fin x1), ∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x4 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) →       have x5 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x5.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x5.inputs;       have x6 : List ℕ := x2.output :: List.flatMap x5 x2.gates;       have x7 : Fin x1 → ℕ := fun (x7 : Fin x1) => (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (x5 x8).contains ↑x7) x2.gates).length;       ∑ x8 : Fin x1, Max.max (1 : ℕ) (x7 x8) + ∑ x8 ∈ Finset.range x2.size, (List.count (x1 + x8) x6 - (1 : ℕ)) + (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op.eval [Bool.false]) x2.gates).length ≤ x2.size + (1 : ℕ) := by
  intro n C hmin hess eff L x
  classical
  obtain ⟨hD, hmn⟩ := hmin
  have hopD : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro g hg
    simpa using (hD g hg).1
  have tk : ∀ g ∈ C.gates, List.take (bif g.op.eval [false] then 1 else 2) g.inputs = L_meta_6502.rds g := by
    intro g hg
    have hl := (hD g hg).2
    rcases hopD g hg with h | h | h
    · simp [L_meta_6502.rds, h, PEqualNP.CircuitLowerBounds.GateOp.eval, List.take_of_length_le hl]
    · simp [L_meta_6502.rds, h, PEqualNP.CircuitLowerBounds.GateOp.eval, List.take_of_length_le hl]
    · simp [L_meta_6502.rds, h, PEqualNP.CircuitLowerBounds.GateOp.eval]
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map L_meta_6502.nrm, C.output⟩
  have hf : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
    funext y
    change (L_meta_6502.run (C.gates.map L_meta_6502.nrm) (List.ofFn y)).getD C.output false = (L_meta_6502.run C.gates (List.ofFn y)).getD C.output false
    rw [L_meta_6502.nrm_run C.gates hopD]
  have hrl : ∀ g ∈ C.gates, (L_meta_6502.rds g).length ≤ 2 := by
    intro g hg
    have := (hD g hg).2
    rcases hopD g hg with h | h | h <;> simp [L_meta_6502.rds, h] <;> omega
  have hFC : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ⟨(hD g' hg').1, hrl g' hg'⟩
  have hlen : C'.gates.length = C.gates.length := by simp [C']
  have he : ∀ g ∈ C.gates, eff g = L_meta_6502.rds g := tk
  -- every gate occurs in the list
  have Hu : ∀ k < C.gates.length, 1 ≤ L.count (n + k) := by
    intro k hk
    rw [Nat.succ_le_iff, List.count_pos_iff]
    by_contra hcon
    simp only [L, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hcon
    obtain ⟨E, hE1, hE2, hE3⟩ := L_meta_6502.del n C' hFC k (by omega) (fun j hj hkj hin => by
      have hj' : j < C.gates.length := by omega
      refine hcon.2 C.gates[j] (List.getElem_mem hj') ?_
      rw [he _ (List.getElem_mem hj')]
      simpa [C', L_meta_6502.nrm] using hin) (fun h => hcon.1 h.symm)
    have h1 := hmn E hE1 (hE3.trans hf)
    have h2 : C'.size = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, C']
    have h3 : C.size = C.gates.length := rfl
    omega
  -- every input occurs in the list
  have Hi : ∀ v : Fin n, 1 ≤ L.count (v : ℕ) := by
    intro v
    rw [Nat.succ_le_iff, List.count_pos_iff]
    by_contra hcon
    simp only [L, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hcon
    obtain ⟨y, z, hyz, hne'⟩ := hess v
    refine hne' ?_
    refine L_meta_6502.indep (v : ℕ) C.gates hopD (fun g hg hin => hcon.2 g hg (by rw [he g hg]; exact hin)) (List.ofFn y) (List.ofFn z) (by simp) ?_ C.output (fun h => hcon.1 h.symm)
    intro q hq
    by_cases hqn : q < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hqn, dif_pos, Option.getD_some]
      exact hyz ⟨q, hqn⟩ (fun h => hq (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hx : ∀ v : Fin n, x v ≤ L.count (v : ℕ) := by
    intro v
    have h1 := L_meta_6502.fcount eff (v : ℕ) C.gates
    have h2 : (List.flatMap eff C.gates).count (v : ℕ) ≤ L.count (v : ℕ) := List.count_le_count_cons
    exact h1.trans h2
  have hlen2 : L.length + (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.op.eval [false]) C.gates).length ≤ 1 + 2 * C.gates.length := by
    have := L_meta_6502.flen eff C.gates (fun g hg => by
      simp only [eff, List.length_take]
      cases g.op.eval [false] <;> simp)
    simp only [L, List.length_cons]
    omega
  have tot := L_meta_6502.csum L ((Finset.univ.image fun v : Fin n => (v : ℕ)) ∪ ((Finset.range C.gates.length).image fun k => n + k))
  rw [Finset.sum_union (by
    refine Finset.disjoint_left.2 fun w h1 h2 => ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨v, rfl⟩ := h1
    obtain ⟨k, _, h⟩ := h2
    have := v.isLt
    omega), Finset.sum_image (fun a _ b _ h => Fin.ext h), Finset.sum_image (fun a _ b _ h => by simpa using h)] at tot
  have b1 : ∑ v : Fin n, max 1 (x v) ≤ ∑ v : Fin n, L.count (v : ℕ) := Finset.sum_le_sum fun v _ => max_le (Hi v) (hx v)
  have b2 : ∑ k ∈ Finset.range C.gates.length, (L.count (n + k) - 1) + C.gates.length ≤ ∑ k ∈ Finset.range C.gates.length, L.count (n + k) := by
    have e : C.gates.length = ∑ k ∈ Finset.range C.gates.length, 1 := by simp
    conv_lhs => rw [show ∑ k ∈ Finset.range C.gates.length, (L.count (n + k) - 1) + C.gates.length = ∑ k ∈ Finset.range C.gates.length, (L.count (n + k) - 1) + ∑ k ∈ Finset.range C.gates.length, 1 by simp]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have := Hu k (Finset.mem_range.1 hk)
    omega
  have h3 : C.size = C.gates.length := rfl
  rw [h3]
  omega

namespace CubicReadCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def front (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

def readers {n : ℕ} (C : Circuit) (v : Fin n) : ℕ :=
  (C.gates.filter fun g => (front g).contains v.val).length

def extra (n : ℕ) (C : Circuit) : ℕ :=
  (∑ j ∈ Finset.range C.size,
    ((C.output :: C.gates.flatMap front).count (n + j) - 1)) +
    (C.gates.filter fun g => g.op.eval [false]).length

def sparse {n : ℕ} (A : Finset (Fin n)) (C : Circuit) : Finset (Fin n) :=
  Aᶜ.filter fun v => readers C v ≤ 1

def triple {n : ℕ} (A : Finset (Fin n)) (C : Circuit) : Finset (Fin n) :=
  Aᶜ.filter fun v => readers C v = 3

private theorem graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) :
    graphFun G A x = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  change (decide (∃ a ∈ A, x a = true) ||
    decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
  simp only [Bool.or_eq_true, decide_eq_true_eq]

private theorem essential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (outside : ∀ u v, G.Adj u v → u ∉ A)
    (eval : circuitFun n C = graphFun G A) (v : Fin n) :
    ∃ x y : Fin n → Bool, (∀ j, j ≠ v → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y := by
  classical
  by_cases hv : v ∈ A
  · let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = v)
    refine ⟨x, y, fun i hi => by simp [x,y,hi], ?_⟩
    rw [eval]
    have hx : graphFun G A x ≠ true := by simp [graph_true,x]
    have hy : graphFun G A y = true := (graph_true G A y).mpr (Or.inl ⟨v,hv,by simp [y]⟩)
    exact fun eq => hx (eq.trans hy)
  · obtain ⟨w, hw⟩ : (G.neighborSet v).Nonempty := (Set.ncard_pos (s := G.neighborSet v)).mp (by rw [deg v hv]; decide)
    have edge : G.Adj v w := hw
    have hwA : w ∉ A := outside w v edge.symm
    let x : Fin n → Bool := fun i => decide (i = w)
    let y : Fin n → Bool := fun i => decide (i = w ∨ i = v)
    refine ⟨x, y, fun i hi => by simp [x,y,hi], ?_⟩
    rw [eval]
    have hx : graphFun G A x ≠ true := by
      intro h
      rcases (graph_true G A x).mp h with ⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩
      · have h : a = w := by simpa [x] using hxa
        exact hwA (h ▸ ha)
      · have h : a = w := by simpa [x] using hxa
        have h' : b = w := by simpa [x] using hxb
        exact hab.ne (h.trans h'.symm)
    have hy : graphFun G A y = true := (graph_true G A y).mpr
      (Or.inr ⟨v,w,edge,by simp [y],by simp [y]⟩)
    exact fun eq => hx (eq.trans hy)

theorem circuit_capacity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (outside : ∀ u v, G.Adj u v → u ∉ A)
    (eval : circuitFun n C = graphFun G A)
    (minimal : IsMinimalCircuit n C) (readCap : ∀ v ∉ A, readers C v ≤ 3) :
    A.card + 2 * Aᶜ.card + (triple A C).card + extra n C ≤
      C.size + 1 + (sparse A C).card := by
  classical
  let r := fun v : Fin n => readers C v
  have count : (∑ v, max 1 (r v)) + extra n C ≤ C.size + 1 := by
    unfold extra
    rw [← Nat.add_assoc]
    exact L_meta_6502 n C minimal (essential G A C deg outside eval)
  have lowerA : A.card ≤ ∑ v ∈ A, max 1 (r v) := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      (Finset.sum_le_sum (f := fun _ : Fin n => 1) (g := fun v => max 1 (r v))
        (s := A) (fun _ _ => le_max_left _ _))
  have split := A.sum_add_sum_compl (fun v => max 1 (r v))
  have terms (v : Fin n) (hv : v ∈ Aᶜ) :
      max 1 (r v) + (if r v ≤ 1 then 1 else 0) = 2 + (if r v = 3 then 1 else 0) := by
    have hr : r v ≤ 3 := readCap v (Finset.mem_compl.mp hv)
    split_ifs <;> omega
  have part1 : (∑ v ∈ Aᶜ, if r v ≤ 1 then (1 : ℕ) else 0) = (sparse A C).card := by
    rw [← Finset.sum_filter]
    simp [sparse, r]
  have part3 : (∑ v ∈ Aᶜ, if r v = 3 then (1 : ℕ) else 0) = (triple A C).card := by
    rw [← Finset.sum_filter]
    simp [triple, r]
  have unmarked := Finset.sum_congr rfl terms
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, part1, part3,
    Finset.sum_const, smul_eq_mul, mul_comm Aᶜ.card 2] at unmarked
  omega

private theorem degree_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  classical
  have outgoing (v : Fin n) :
      (Finset.univ.filter fun d : G.Dart => d.fst = v) =
        Finset.univ.image (G.dartOfNeighborSet v) := by
    ext d
    simp only [Finset.mem_image, true_and, Finset.mem_filter, SetCoe.exists, Finset.mem_univ]
    constructor
    · rintro rfl
      exact ⟨_, d.adj, by ext <;> rfl⟩
    · rintro ⟨e, he, rfl⟩
      rfl
  have count_outgoing (v : Fin n) :
      (Finset.univ.filter fun d : G.Dart => d.fst = v).card = G.degree v := by
    simpa only [outgoing, Finset.card_univ, G.card_neighborSet_eq_degree] using
      Finset.card_image_of_injective Finset.univ (G.dartOfNeighborSet_injective v)
  have outgoing_sum : Fintype.card G.Dart = ∑ v, G.degree v := by
    simp only [← Finset.card_univ, ← count_outgoing]
    exact Finset.card_eq_sum_card_fiberwise (by simp)
  have fiber (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet) :
      (Finset.univ.filter fun d : G.Dart => d.edge = e).card = 2 := by
    obtain ⟨v,w⟩ := e
    let d : G.Dart := ⟨(v,w),he⟩
    have heq : (Finset.univ.filter fun d' : G.Dart => d'.edge = d.edge) = {d,d.symm} :=
      Finset.ext fun d' => by simpa using SimpleGraph.dart_edge_eq_iff d' d
    change (Finset.univ.filter fun d' : G.Dart => d'.edge = d.edge).card = _
    rw [heq, Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    exact d.symm_ne.symm
  have edge_sum : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
    rw [← Finset.card_univ]
    rw [@Finset.card_eq_sum_card_fiberwise _ _ _ SimpleGraph.Dart.edge _ G.edgeFinset
      fun d _ => by rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset]; apply SimpleGraph.Dart.edge_mem]
    rw [← Nat.mul_comm, Finset.sum_const_nat]
    intro e h
    exact fiber e (SimpleGraph.mem_edgeFinset.mp h)
  exact outgoing_sum.symm.trans edge_sum

theorem benchmark_of_slots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (outside : ∀ u v, G.Adj u v → u ∉ A)
    (eval : circuitFun n C = graphFun G A)
    (minimal : IsMinimalCircuit n C) (readCap : ∀ v ∉ A, readers C v ≤ 3)
    (I : Finset (Fin n)) (sub : I ⊆ Aᶜ)
    (indep : ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w)
    (charge : Aᶜ.card + 2 * (sparse A C).card ≤
      2 * ((triple A C).card + extra n C + I.card)) :
    ∃ T : Finset (Fin n), Disjoint A T ∧
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      A.card + G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  let T := Aᶜ \ I
  have hT : T.card + I.card = Aᶜ.card := Finset.card_sdiff_add_card_eq_card sub
  have dA (v : Fin n) (hv : v ∈ A) : G.degree v = 0 :=
    (G.degree_eq_zero v).mpr fun w hadj => outside v w hadj hv
  have dB (v : Fin n) (hv : v ∈ Aᶜ) : G.degree v = 3 :=
    (G.ncard_neighborSet v).symm.trans (deg v (Finset.mem_compl.mp hv))
  have degrees := degree_sum G
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degrees
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degrees
  refine ⟨T, Finset.disjoint_left.mpr (fun v hv ht => ?_), ?_, ?_⟩
  · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp ht).1) hv
  · intro v w hadj
    have hv := Finset.mem_compl.mpr (outside v w hadj)
    have hw := Finset.mem_compl.mpr (outside w v hadj.symm)
    by_cases h : v ∈ I
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hw, fun h' => indep v h w h' hadj⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hv,h⟩)
  · have cap := circuit_capacity G A C deg outside eval minimal readCap
    omega

end CubicReadCount


namespace L_meta_4009_aux


namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end H926

namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end H926

namespace H926
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

theorem orChain (k : ℕ) : ∀ m : ℕ, k + 1 ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = k ∧ out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = decide (∃ i : Fin (k + 1), w.getD i false = true) := by
  induction k with
  | zero =>
    intro m hm
    refine ⟨[], 0, by simp, rfl, by simp; omega, ?_⟩
    intro w _
    simp [wiresFrom]
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [⟨GateOp.or, [out, k + 1]⟩], m + gs.length, ?_, by simp [len], by simp, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      set v := wiresFrom gs w with hv
      have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
      have e1 : v.getD (k + 1) false = w.getD (k + 1) false := by
        rw [hv, getD_wiresFrom _ _ _ (by omega)]
      have step : wiresFrom [⟨GateOp.or, [out, k + 1]⟩] v
          = v ++ [GateOp.or.eval ([out, k + 1].map fun i => v.getD i false)] := rfl
      rw [step, ← lv, getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [ev w hw, e1]
      simp [Fin.exists_fin_succ']

theorem or_size (n s : ℕ) :
    HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true)) s ↔ n ≤ s + 1 := by
  constructor
  · apply dep_lower
    intro i
    refine ⟨fun _ => false, ?_⟩
    simp only [Bool.not_false, ne_eq]
    have h1 : (∃ j : Fin n, Function.update (fun _ : Fin n => false) i true j = true) :=
      ⟨i, by simp⟩
    simp [h1]
  · intro h
    cases n with
    | zero =>
      refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
      intro x
      simp [Circuit.eval, Circuit.wires]
    | succ k =>
      obtain ⟨gs, out, ok, len, _, ev⟩ := orChain k (k + 1) le_rfl
      refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; omega, ?_⟩
      intro x
      have h := ev (List.ofFn x) (by simp)
      simp only [Circuit.eval, wires_eq, h, getD_ofFn]

end H926

namespace H926.EdgeUpper
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds H926

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem bld_graph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) (hE : ∃ i j : Fin n, G.Adj i j) (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) : Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S T : Finset (Fin n)) (s : ℕ) (h1 : S.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) (hs : s + 1 = S.card + G.edgeFinset.card + T.card) : PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((∃ v ∈ S, x v = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s := by
  apply bld_hasCircuitSize
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · have hg := bld_graph n G T hE hc
    have hpos : 0 < G.edgeFinset.card := by
      obtain ⟨i0, j0, h0⟩ := hE
      exact Finset.card_pos.2 ⟨s(i0, j0), by simpa using h0⟩
    by_cases hS : S.Nonempty
    · have hp := hS.card_pos
      refine bld_congr (bld_mono (bld_or (bld_anyFinset S hS) hg) (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff]
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      refine bld_congr (bld_mono hg (by simp at hs; omega)) ?_
      intro x
      simp
  · have hS : S.Nonempty := h1.resolve_right hE
    refine bld_congr (bld_mono (bld_anyFinset S hS) (by omega)) ?_
    intro x
    rw [decide_eq_decide]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨i, j, hij, _⟩)
      · exact h
      · exact absurd ⟨i, j, hij⟩ hE

end H926.EdgeUpper

end L_meta_4009_aux

theorem L_meta_4009 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : ℕ), (x4.Nonempty ∨ ∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∈ x5 ∨ x9 ∈ x5) → x6 + (1 : ℕ) = x4.card + x2.edgeFinset.card + x5.card → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x10 : Fin x1 → Bool) => Decidable.decide ((∃ x11 ∈ x4, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true)) x6 := by
  intro x1 x2 x3 x4 x5 x6 h1 h2 h3
  exact L_meta_4009_aux.H926.EdgeUpper.main x1 x2 x4 x5 x6 h1 h2 h3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open CubicReadCount
open scoped BigOperators

theorem all_two_neighborhood (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (girth : ∀ u (p : G.Walk u u), p.IsCycle → 7 ≤ p.length)
    (outside : ∀ v w, G.Adj v w → v ∉ A)
    (edge : ∃ v w, G.Adj v w)
    (fan : FanInTwo C) (eval : circuitFun n C = graphFun G A)
    (minimum : ∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s)
    (readRange : ∀ v ∉ A, 2 ≤ readers C v ∧ readers C v ≤ 3) :
    ∃ v ∉ A, readers C v = 2 ∧ ∀ w, G.Adj v w → readers C w = 2 := by
  classical
  by_contra no
  let B := Aᶜ
  let H := triple A C
  let closed : Fin n → Finset (Fin n) := fun v => insert v (G.neighborFinset v)
  have three (v : Fin n) (hB : v ∈ B) (h : readers C v = 3) : v ∈ H := by
    exact Finset.mem_filter.mpr ⟨hB,h⟩
  have covered : B ⊆ H.biUnion closed := by
    intro v hB
    have hvA := Finset.mem_compl.mp hB
    have pr := readRange v hvA
    by_cases h : readers C v = 3
    · exact Finset.mem_biUnion.mpr ⟨v,three v hB h,Finset.mem_insert_self _ _⟩
    · have hTwo : readers C v = 2 := by omega
      have nbr : ∃ w, G.Adj v w ∧ readers C w ≠ 2 := by
        by_contra! all
        exact no ⟨v,hvA,hTwo,all⟩
      obtain ⟨w,e,hw⟩ := nbr
      have hwA := outside w v e.symm
      have wr := readRange w hwA
      refine Finset.mem_biUnion.mpr ⟨w,three w (Finset.mem_compl.mpr hwA) (by omega),?_⟩
      exact Finset.mem_insert_of_mem ((G.mem_neighborFinset w v).mpr e.symm)
  have eachClosed : ∀ v ∈ H, (closed v).card ≤ 4 := by
    intro v hv
    have hvA := Finset.mem_compl.mp (Finset.mem_filter.mp hv).1
    have hdeg : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (deg v hvA)
    dsimp [closed]
    rw [Finset.card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,hdeg]
  have dom : B.card ≤ 4 * H.card := by
    have h := (Finset.card_le_card covered).trans (Finset.card_biUnion_le_card_mul H closed 4 eachClosed)
    simpa only [Nat.mul_comm] using h
  obtain ⟨a,b,he⟩ := edge
  have bp : 0 < B.card := Finset.card_pos.mpr ⟨a,Finset.mem_compl.mpr (outside a b he)⟩
  have ep : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(a,b),SimpleGraph.mem_edgeFinset.mpr he⟩
  obtain ⟨I,hI,independent,packing⟩ := L_meta_6500 n G B
    (fun _ _ _ e => Finset.mem_compl.mpr (outside _ _ e.symm))
    (fun v hv => deg v (Finset.mem_compl.mp hv)) girth
  let T := B \ I
  have sumCards : T.card + I.card = B.card := Finset.card_sdiff_add_card_eq_card hI
  have cover (v w : Fin n) (e : G.Adj v w) : v ∈ T ∨ w ∈ T := by
    have vb := Finset.mem_compl.mpr (outside v w e)
    have wb := Finset.mem_compl.mpr (outside w v e.symm)
    by_cases vi : v ∈ I
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨wb,fun wi => independent v vi w wi e⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨vb,vi⟩)
  have minC : IsMinimalCircuit n C := ⟨fan, by
    intro D fd same
    apply minimum D.size
    exact ⟨D,fd,le_rfl,fun x => congrFun (same.trans eval) x⟩⟩
  have sZero : sparse A C = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨vb,bnd⟩ := Finset.mem_filter.mp hv
    have hl := (readRange v (Finset.mem_compl.mp vb)).1
    omega
  have cap := circuit_capacity G A C deg outside eval minC (fun v hv => (readRange v hv).2)
  rw [sZero,Finset.card_empty,Nat.add_zero] at cap
  have cap' : A.card + 2*B.card + H.card ≤ C.size + 1 := by
    change A.card + 2*B.card + H.card + extra n C ≤ C.size + 1 at cap
    omega
  have dA (v : Fin n) (hv : v ∈ A) : G.degree v = 0 :=
    (G.degree_eq_zero v).mpr fun w e => outside v w e hv
  have dB (v : Fin n) (hv : v ∈ Aᶜ) : G.degree v = 3 :=
    (G.ncard_neighborSet v).symm.trans (deg v (Finset.mem_compl.mp hv))
  have degrees := degree_sum G
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degrees
  simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul] at degrees
  change B.card * 3 = 2 * G.edgeFinset.card at degrees
  let q := A.card + G.edgeFinset.card + T.card - 1
  have qb : q+1 = A.card + G.edgeFinset.card + T.card := by dsimp [q]; omega
  have eqFun :
      (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨
        ∃ v w, G.Adj v w ∧ x v = true ∧ x w = true)) = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq,graph_true]
  have upper := minimum q (eqFun ▸ L_meta_4009 n G A T q (Or.inr ⟨a,b,he⟩) cover qb)
  omega

end PEqualNP.Outside.L_meta_18457

theorem PEqualNP.Outside.L_meta_18457 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → ℕ := fun (x7 : Fin x1) => (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates).length;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ x7 x15 ∧ x7 x15 ≤ (3 : ℕ)) → ∃ x16 ∉ x4, x7 x16 = (2 : ℕ) ∧ ∀ (x17 : Fin x1), x2.Adj x16 x17 → x7 x17 = (2 : ℕ)) := PEqualNP.Outside.L_meta_18457.all_two_neighborhood
