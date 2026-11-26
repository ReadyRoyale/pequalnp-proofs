import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18502_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def compile (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 = true then .and else .or, [g.2.1, g.2.2]⟩

private def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def valueS {α : Type} (w : List (Set α)) (g : Bool × ℕ × ℕ) : Set α :=
  if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅
  else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅

private def stepS {α : Type} (w : List (Set α)) (g : Bool × ℕ × ℕ) : List (Set α) :=
  w.concat (valueS w g)

private def Related {α : Type} (p : α) (w : List Bool) (s : List (Set α)) : Prop :=
  w.length = s.length ∧ ∀ i, w.getD i false = true ↔ p ∈ s.getD i ∅

private theorem before_next {α : Type} (l : List α) (v d : α) (i : ℕ) (h : i ≠ l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem step_related {α : Type} (p : α) (w : List Bool) (s : List (Set α))
    (rel : Related p w s) (g : Bool × ℕ × ℕ) :
    Related p (stepB w (compile g)) (stepS s g) := by
  let valueB := (compile g).op.eval ((compile g).inputs.map fun i => w.getD i false)
  have hn : valueB = true ↔ p ∈ valueS s g := by
    rcases g with ⟨flag, u, v⟩
    cases flag <;> simp [valueB, compile, GateOp.eval, valueS]
    · simpa only [List.getD_eq_getElem?_getD] using or_congr (rel.2 u) (rel.2 v)
    · simpa only [List.getD_eq_getElem?_getD] using and_congr (rel.2 u) (rel.2 v)
  refine ⟨by simp [stepB, stepS, rel.1], ?_⟩
  intro i
  change (w ++ [valueB]).getD i false = true ↔ p ∈ (s.concat (valueS s g)).getD i ∅
  rw [List.concat_eq_append]
  by_cases h : i = w.length
  · subst i
    have hw : (w ++ [valueB]).getD w.length false = valueB := by simp
    have hs : (s ++ [valueS s g]).getD w.length ∅ = valueS s g := by simp [rel.1]
    rwa [hw, hs]
  · have hs : i ≠ s.length := by rwa [← rel.1]
    rw [before_next _ _ _ _ h, before_next _ _ _ _ hs]
    exact rel.2 i

private theorem fold_related {α : Type} (p : α) (gs : List (Bool × ℕ × ℕ))
    (w : List Bool) (s : List (Set α)) (rel : Related p w s) :
    Related p ((gs.map compile).foldl stepB w) (gs.foldl stepS s) := by
  induction gs generalizing w s with
  | nil => exact rel
  | cons g gs ih => exact ih _ _ (step_related p w s rel g)

private abbrev Pair := Finset (Fin 13) × Finset (Fin 13)

theorem result (inputs : Fin 25 → Set Pair) (gs : List (Bool × ℕ × ℕ)) (out : ℕ) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = gs.length ∧ C.output = out ∧
      ∀ (p : Pair) (x : Fin 25 → Bool), (∀ i, x i = true ↔ p ∈ inputs i) →
        ∀ i, (C.wires (List.ofFn x)).getD i false = true ↔
          p ∈ (gs.foldl stepS (List.ofFn inputs)).getD i ∅ := by
  refine ⟨⟨gs.map compile, out⟩, ?_, by simp [Circuit.size], rfl, ?_⟩
  · intro g hg
    obtain ⟨⟨flag, u, v⟩, _, rfl⟩ := List.mem_map.mp hg
    cases flag <;> simp [compile]
  · intro p x hx i
    have initial : Related p (List.ofFn x) (List.ofFn inputs) := by
      refine ⟨by simp, ?_⟩
      intro j
      by_cases hj : j < 25
      · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj, Option.getD_some]
          using hx ⟨j, hj⟩
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hj, Option.getD_none,
          Bool.false_eq_true, Set.notMem_empty]
    exact (fold_related p gs _ _ initial).2 i

end PEqualNP.Outside.L_meta_18502_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18502 :
    have Pair : Type := Finset (Fin 13) × Finset (Fin 13)
    ∀ (inputs : Fin 25 → Set Pair) (gs : List (Bool × ℕ × ℕ)) (out : ℕ),
      ∃ C : Circuit, Monotone2 C ∧ C.size = gs.length ∧ C.output = out ∧
        ∀ (p : Pair) (x : Fin 25 → Bool), (∀ i, x i = true ↔ p ∈ inputs i) →
          ∀ i, (C.wires (List.ofFn x)).getD i false = true ↔
            p ∈ (List.foldl (fun (w : List (Set Pair)) (g : Bool × ℕ × ℕ) =>
              w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅
                else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)) (List.ofFn inputs) gs).getD i ∅ :=
  PEqualNP.Outside.L_meta_18502_aux.result
