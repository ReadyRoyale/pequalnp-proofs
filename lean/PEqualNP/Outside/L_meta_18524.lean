import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18524_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def LEWire (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, w.getD i false = true → v.getD i false = true

private theorem oldWire (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem gate_mono (g : Gate) (hOp : g.op = .and ∨ g.op = .or)
    {w v : List Bool} (rel : LEWire w v) : LEWire (step w g) (step v g) := by
  have hd (i : ℕ) : w.getD i false = true → v.getD i false = true := rel.2 i
  let left := g.op.eval (g.inputs.map fun i => w.getD i false)
  let right := g.op.eval (g.inputs.map fun i => v.getD i false)
  have hNew : left = true → right = true := by
    rcases hOp with h | h
    · simp only [left, right, h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
      exact fun hw i hi => hd i (hw i hi)
    · simp only [left, right, h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      rintro ⟨i, hi, good⟩
      exact ⟨i, hi, hd i good⟩
  refine ⟨by simp [step, rel.1], ?_⟩
  intro i
  change (w ++ [left]).getD i false = true → (v ++ [right]).getD i false = true
  by_cases hi : i = w.length
  · subst i
    have hw : (w ++ [left]).getD w.length false = left := by simp
    have hv : (v ++ [right]).getD w.length false = right := by simp [rel.1]
    rwa [hw, hv]
  · have hv : i ≠ v.length := by rwa [← rel.1]
    rw [oldWire w left i hi, oldWire v right i hv]
    exact hd i

private theorem fold_mono (gs : List Gate) (hOp : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (w v : List Bool) (rel : LEWire w v) : LEWire (gs.foldl step w) (gs.foldl step v) := by
  induction gs generalizing w v with
  | nil => exact rel
  | cons g gs ih =>
    exact ih (fun k hk => hOp k (List.mem_cons_of_mem _ hk)) _ _ (gate_mono g (hOp g (by simp)) rel)

private theorem eval_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (hle : ∀ i, x i = true → y i = true)
    (h : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  have rel : LEWire (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < n
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
        using hle ⟨i, hi⟩
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi, Option.getD_none,
        Bool.false_eq_true, imp_self]
  exact (fold_mono C.gates hC.1 _ _ rel).2 C.output h

private def Edge (i j : Fin 7) : Prop := i = j ∨ i = j + 1 ∨ i = j + 3
private def Left (i : Fin 7) : Fin 14 := Fin.castAdd 7 i
private def Right (i : Fin 7) : Fin 14 := Fin.natAdd 7 i
private def Present (x : Fin 14 → Bool) (i j : Fin 7) : Prop :=
  Edge i j ∧ x (Left i) = true ∧ x (Right j) = true
private def Independent (x : Fin 14 → Bool) : Prop := ¬ ∃ i j, Present x i j

theorem result (C : Circuit) (hC : IsAO2 14 C)
    (positive : ∀ i j : Fin 7, j ≠ 1 → Edge i j →
      C.eval (List.ofFn fun k : Fin 14 => decide (k = Left i ∨ k = Right j)) = true)
    (negative : ∀ x : Fin 14 → Bool, Maximal Independent x → C.eval (List.ofFn x) = false)
    (x : Fin 14 → Bool) :
    (C.eval (List.ofFn x) = true → ∃ i j, Present x i j) ∧
    ((∃ i j, j ≠ 1 ∧ Present x i j) → C.eval (List.ofFn x) = true) := by
  classical
  constructor
  · intro hx
    by_contra hInd
    obtain ⟨y, hxy, hy⟩ := Finite.exists_le_maximal (p := Independent) hInd
    have hImp (i : Fin 14) (hi : x i = true) : y i = true := by
      cases hyi : y i
      · have lower := hxy i
        rw [hi, hyi] at lower
        exact ((by decide : ¬ (true ≤ false)) lower).elim
      · rfl
    have hyTrue := eval_mono C hC x y hImp hx
    exact Bool.false_ne_true ((negative y hy).symm.trans hyTrue)
  · rintro ⟨i, j, hj, edge, hl, hr⟩
    apply eval_mono C hC (fun k : Fin 14 => decide (k = Left i ∨ k = Right j)) x _ (positive i j hj edge)
    intro k hk
    have equal : k = Left i ∨ k = Right j := of_decide_eq_true hk
    rcases equal with rfl | rfl
    · exact hl
    · exact hr

end PEqualNP.Outside.L_meta_18524_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm in
theorem PEqualNP.Outside.L_meta_18524 :
    ∀ (C : Circuit), IsAO2 14 C →
      (∀ i j : Fin 7, j ≠ 1 → (i = j ∨ i = j + 1 ∨ i = j + 3) →
        C.eval (List.ofFn fun k : Fin 14 => decide (k = Fin.castAdd 7 i ∨ k = Fin.natAdd 7 j)) = true) →
      (∀ x : Fin 14 → Bool,
        Maximal (fun y : Fin 14 → Bool => ¬ ∃ i j : Fin 7,
          (i = j ∨ i = j + 1 ∨ i = j + 3) ∧ y (Fin.castAdd 7 i) = true ∧
            y (Fin.natAdd 7 j) = true) x → C.eval (List.ofFn x) = false) →
      ∀ x : Fin 14 → Bool,
        (C.eval (List.ofFn x) = true → ∃ i j : Fin 7,
          (i = j ∨ i = j + 1 ∨ i = j + 3) ∧ x (Fin.castAdd 7 i) = true ∧
            x (Fin.natAdd 7 j) = true) ∧
        ((∃ i j : Fin 7, j ≠ 1 ∧ (i = j ∨ i = j + 1 ∨ i = j + 3) ∧
          x (Fin.castAdd 7 i) = true ∧ x (Fin.natAdd 7 j) = true) → C.eval (List.ofFn x) = true) :=
  PEqualNP.Outside.L_meta_18524_aux.result
