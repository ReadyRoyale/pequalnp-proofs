import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18507_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def shifted (offset : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (offset + ·)⟩

private theorem shift_step (raw w : List Bool) (g : Gate) :
    step (raw ++ w) (shifted raw.length g) = raw ++ step w g := by
  have hMap : (g.inputs.map (raw.length + ·)).map (fun i => (raw ++ w).getD i false) =
      g.inputs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    change (raw ++ w).getD (raw.length + i) false = w.getD i false
    rw [List.getD_append_right _ _ _ _ (by omega), show raw.length + i - raw.length = i by omega]
  simp only [step, shifted]
  rw [hMap, List.append_assoc]

private theorem shift_fold (raw : List Bool) (gs : List Gate) (w : List Bool) :
    (gs.map (shifted raw.length)).foldl step (raw ++ w) = raw ++ gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, shift_step]
    exact ih _

private def fuse {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Gate :=
  ⟨.or, [i.val, n + (π i).val]⟩

private def fuseValue {n : ℕ} (π : Equiv.Perm (Fin n)) (raw : List Bool) (i : Fin n) : Bool :=
  raw.getD i.val false || raw.getD (n + (π i).val) false

private theorem fuse_fold {n : ℕ} (π : Equiv.Perm (Fin n)) (raw : List Bool)
    (hraw : raw.length = n + n) (is : List (Fin n)) (tail : List Bool) :
    (is.map (fuse π)).foldl step (raw ++ tail) = raw ++ tail ++ is.map (fuseValue π raw) := by
  induction is generalizing tail with
  | nil => simp
  | cons i is ih =>
    have hLeft : i.val < raw.length := by have := i.isLt; omega
    have hRight : n + (π i).val < raw.length := by have := (π i).isLt; omega
    have hStep : step (raw ++ tail) (fuse π i) = raw ++ (tail ++ [fuseValue π raw i]) := by
      simp only [step, fuse, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, id, Bool.or_false, fuseValue]
      rw [List.getD_append _ _ _ _ hLeft, List.getD_append _ _ _ _ hRight, List.append_assoc]
    simp only [List.map_cons, List.foldl_cons]
    rw [hStep, ih]
    simp [List.append_assoc]

private theorem read_marked {n : ℕ} (u i : Fin n) :
    (List.ofFn fun j : Fin n => decide (j = u)).getD i.val false = decide (i = u) := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

private theorem fuse_marked {n : ℕ} (π : Equiv.Perm (Fin n)) (u v i : Fin n) :
    fuseValue π (oneEach u v) i = decide (i = u ∨ i = π.symm v) := by
  let left := List.ofFn (fun j : Fin n => decide (j = u))
  let right := List.ofFn (fun j : Fin n => decide (j = v))
  have ln : left.length = n := by simp [left]
  have ei : π i = v ↔ i = π.symm v := by
    constructor
    · intro e
      simpa using congrArg π.symm e
    · intro e
      simpa using congrArg π e
  change ((left ++ right).getD i.val false || (left ++ right).getD (n + (π i).val) false) = _
  rw [List.getD_append _ _ _ _ (by rw [ln]; exact i.isLt),
    List.getD_append_right _ _ _ _ (by omega), ln, show n + (π i).val - n = (π i).val by omega]
  have atL : left.getD i.val false = decide (i = u) := read_marked u i
  have atR : right.getD (π i).val false = decide (π i = v) := read_marked v (π i)
  rw [atL, atR]
  simp [ei]

private theorem fuse_inputs {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    (List.ofFn (fuse π)).foldl step (oneEach u v) =
      oneEach u v ++ List.ofFn (fun i : Fin n => decide (i = u ∨ i = π.symm v)) := by
  have hl : (oneEach u v).length = n + n := by simp [oneEach]
  have h := fuse_fold π (oneEach u v) hl (List.ofFn fun i : Fin n => i) []
  simpa only [List.append_nil, List.map_ofFn, Function.comp_def, fuse_marked] using h

theorem result (n s : ℕ) (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (diag : ∀ a, H a a = false)
    (given : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      (∀ a : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = a)) = false) ∧
      (∀ a b : Fin n, a ≠ b → C.eval (List.ofFn fun i : Fin n => decide (i = a ∨ i = b)) = H a b)) :
    RepSizeAtMost (fun u v : Fin n => H u (π.symm v)) (n + s) := by
  obtain ⟨C, good, size, single, pair⟩ := given
  let D : Circuit :=
    ⟨List.ofFn (fuse π) ++ C.gates.map (shifted (n + n)), (n + n) + C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ List.ofFn (fuse π) ++ C.gates.map (shifted (n + n)) at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      simp [fuse]
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(good g' hg').1, by simpa [shifted] using (good g' hg').2⟩
  · simpa [D, Circuit.size] using Nat.add_le_add_left size n
  · intro u v
    let raw := oneEach u v
    let fused : Fin n → Bool := fun i => decide (i = u ∨ i = π.symm v)
    have hl : raw.length = n + n := by simp [raw, oneEach]
    have wires : D.wires raw = raw ++ C.wires (List.ofFn fused) := by
      change (List.ofFn (fuse π) ++ C.gates.map (shifted (n + n))).foldl step raw =
        raw ++ C.gates.foldl step (List.ofFn fused)
      rw [List.foldl_append, fuse_inputs π u v, ← hl, shift_fold]
    have eval : D.eval raw = C.eval (List.ofFn fused) := by
      change (D.wires raw).getD (n + n + C.output) false = (C.wires (List.ofFn fused)).getD C.output false
      rw [wires, List.getD_append_right _ _ _ _ (by omega), hl,
        show n + n + C.output - (n + n) = C.output by omega]
    change D.eval raw = H u (π.symm v)
    rw [eval]
    by_cases same : u = π.symm v
    · have eq : fused = fun i : Fin n => decide (i = u) := by funext i; simp [fused, ← same]
      rw [eq, single u, ← same, diag]
    · exact pair u (π.symm v) same

end PEqualNP.Outside.L_meta_18507_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_18507 :
    ∀ (n s : ℕ) (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)),
      (∀ a b, H a b = H b a) → (∀ a, H a a = false) →
      (∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
        (∀ a : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = a)) = false) ∧
        (∀ a b : Fin n, a ≠ b → C.eval (List.ofFn fun i : Fin n => decide (i = a ∨ i = b)) = H a b)) →
      RepSizeAtMost (fun u v : Fin n => H u (π.symm v)) (n + s) := by
  intro n s H π _ diag given
  exact PEqualNP.Outside.L_meta_18507_aux.result n s H π diag given
