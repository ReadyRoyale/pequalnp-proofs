import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18543

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.BlindGate

def gate (op : GateOp) (a b : ℕ) : Gate := ⟨op, [a, b]⟩

def tail (t o : ℕ) (u : Fin 13 → ℕ) : List Gate :=
  [gate .or 0 1, gate .or 3 9, gate .or t (t+1), gate .or o (t+2),
   gate .and 0 (u 0), gate .and 1 (u 1), gate .and 3 (u 3), gate .and 9 (u 9),
   gate .or (t+4) (t+5), gate .or (t+6) (t+7), gate .or (t+8) (t+9),
   gate .or o (t+10), gate .or (t+11) 13, gate .and (t+3) (t+12)]

def extend (C : Circuit) (u : Fin 13 → ℕ) : Circuit :=
  ⟨C.gates ++ tail (26+C.gates.length) C.output u, 26+C.gates.length+13⟩

theorem singer_zero : singerLines3 (0 : Fin 13) = ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide +kernel

def Good (lim : ℕ) (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
    g.inputs.Nodup ∧ ∀ i ∈ g.inputs, i < lim

theorem tail_good (t o : ℕ) (u : Fin 13 → ℕ) (ht : 26 ≤ t) (ho : o < t)
    (hu : ∀ p ∈ singerLines3 0, u p < t ∧ u p ≠ p.val)
    (j : ℕ) (hj : j < 14) :
    Good (t+j) ((tail t o u).getD j ⟨.or, []⟩) := by
  have hu0 := hu 0 (by decide +kernel)
  have hu1 := hu 1 (by decide +kernel)
  have hu3 := hu 3 (by decide +kernel)
  have hu9 := hu 9 (by decide +kernel)
  simp only [Fin.val_zero, Fin.val_one] at hu0 hu1 hu3 hu9
  interval_cases j <;> simp [tail, gate, Good] <;> omega

theorem extend_good (C : Circuit) (u : Fin 13 → ℕ) (hC : IsAO2 26 C)
    (hd : ∀ g ∈ C.gates, g.inputs.Nodup) (ho : C.output < 26+C.gates.length)
    (hu : ∀ p ∈ singerLines3 0, u p < 26+C.gates.length ∧ u p ≠ p.val) :
    IsAO2 26 (extend C u) ∧ ∀ g ∈ (extend C u).gates, g.inputs.Nodup := by
  have at_good : ∀ j < (extend C u).gates.length,
      Good (26+j) (gateAt (extend C u) j) := by
    intro j hj
    by_cases h : j < C.gates.length
    · have heq : gateAt (extend C u) j = gateAt C j :=
        List.getD_append _ _ _ _ h
      have hm : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ h]
        exact List.getElem_mem h
      rw [heq]
      exact ⟨hC.1 _ hm, hC.2.2 _ hm, hd _ hm, hC.2.1 j h⟩
    · let t := 26+C.gates.length
      let k := j-C.gates.length
      have hk : k < 14 := by
        simp [extend, tail] at hj
        dsimp [k]
        omega
      have heq : gateAt (extend C u) j = (tail t C.output u).getD k ⟨.or, []⟩ :=
        List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)
      have hlim : 26+j = t+k := by dsimp [t, k]; omega
      rw [heq, hlim]
      exact tail_good t C.output u (by dsimp [t]; omega) ho hu k hk
  have member_good : ∀ g ∈ (extend C u).gates,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hit := at_good j hj
    rw [gateAt, List.getD_eq_getElem _ _ hj] at hit
    exact ⟨hit.1, hit.2.1, hit.2.2.1⟩
  exact ⟨⟨fun g hg => (member_good g hg).1, fun j hj => (at_good j hj).2.2.2,
    fun g hg => (member_good g hg).2.1⟩, fun g hg => (member_good g hg).2.2⟩

def push (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl push w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [push]
      omega

theorem run_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl push w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [push]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem read_old (w : List Bool) {i : ℕ} (hi : i < w.length) (xs : List Bool) :
    (w ++ xs).getD i false = w.getD i false :=
  List.getD_append _ _ _ _ hi

theorem read_new (w xs : List Bool) (j : ℕ) :
    (w ++ xs).getD (w.length+j) false = xs.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem read_new_zero (w xs : List Bool) :
    (w ++ xs).getD w.length false = xs.getD 0 false := by
  simpa only [Nat.add_zero] using read_new w xs 0

theorem push_or (w xs : List Bool) (a b : ℕ) :
    push (w ++ xs) (gate .or a b) =
      w ++ (xs ++ [(w ++ xs).getD a false || (w ++ xs).getD b false]) := by
  simp [push, gate, GateOp.eval, List.append_assoc]

theorem push_and (w xs : List Bool) (a b : ℕ) :
    push (w ++ xs) (gate .and a b) =
      w ++ (xs ++ [(w ++ xs).getD a false && (w ++ xs).getD b false]) := by
  simp [push, gate, GateOp.eval, List.append_assoc]

def tail_bits (w : List Bool) (o : ℕ) (u : Fin 13 → ℕ) : List Bool :=
  let b := fun i => w.getD i false
  let p01 := b 0 || b 1
  let p39 := b 3 || b 9
  let p := p01 || p39
  let a := b o || p
  let m0 := b 0 && b (u 0)
  let m1 := b 1 && b (u 1)
  let m3 := b 3 && b (u 3)
  let m9 := b 9 && b (u 9)
  let m01 := m0 || m1
  let m39 := m3 || m9
  let m := m01 || m39
  let d := b o || m
  let e := d || b 13
  [p01, p39, p, a, m0, m1, m3, m9, m01, m39, m, d, e, a && e]

set_option maxHeartbeats 1800000 in
theorem tail_run (w : List Bool) (o : ℕ) (u : Fin 13 → ℕ)
    (hw : 26 ≤ w.length) (ho : o < w.length)
    (hu : ∀ p ∈ singerLines3 0, u p < w.length) :
    (tail w.length o u).foldl push w = w ++ tail_bits w o u := by
  have hu0 := hu 0 (by decide +kernel)
  have hu1 := hu 1 (by decide +kernel)
  have hu3 := hu 3 (by decide +kernel)
  have hu9 := hu 9 (by decide +kernel)
  calc
    _ = (tail w.length o u).foldl push (w ++ []) := by rw [List.append_nil]
    _ = _ := by
      simp only [tail, tail_bits, List.foldl_cons, List.foldl_nil, push_or, push_and,
        read_old w (show 0 < w.length by omega), read_old w (show 1 < w.length by omega),
        read_old w (show 3 < w.length by omega), read_old w (show 9 < w.length by omega),
        read_old w (show 13 < w.length by omega), read_old w ho,
        read_old w hu0, read_old w hu1, read_old w hu3, read_old w hu9, read_new_zero,
        read_new, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]

theorem any_point (f : Fin 13 → Bool) :
    decide (∃ i ∈ singerLines3 0, f i = true) =
      ((f 0 || f 1) || (f 3 || f 9)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, hf⟩
    rw [singer_zero] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [hf]
  · rintro ((h | h) | (h | h))
    · exact ⟨0, by decide +kernel, h⟩
    · exact ⟨1, by decide +kernel, h⟩
    · exact ⟨3, by decide +kernel, h⟩
    · exact ⟨9, by decide +kernel, h⟩

theorem wire_input (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  change (C.gates.foldl push (List.ofFn x)).getD i false = x i
  rw [run_read _ _ _ hi, List.getD_eq_getElem _ _ hi]
  exact List.getElem_ofFn hi

theorem operand_values (C : Circuit) (u : Fin 13 → ℕ)
    (ho : C.output < 26+C.gates.length)
    (hu : ∀ p ∈ singerLines3 0, u p < 26+C.gates.length) (x : Fin 26 → Bool) :
    wireValue (extend C u) 26 x (26+C.gates.length+3) =
      (C.eval (List.ofFn x) ||
        decide (∃ i ∈ singerLines3 0, x (Fin.castAdd 13 i) = true)) ∧
    wireValue (extend C u) 26 x (26+C.gates.length+12) =
      (C.eval (List.ofFn x) ||
        decide (∃ i ∈ singerLines3 0,
          x (Fin.castAdd 13 i) = true ∧ wireValue C 26 x (u i) = true) || x 13) := by
  let w := C.wires (List.ofFn x)
  have hw : w.length = 26+C.gates.length := by
    change (C.gates.foldl push (List.ofFn x)).length = 26+C.gates.length
    rw [run_length, List.length_ofFn]
  have combined : (extend C u).wires (List.ofFn x) = w ++ tail_bits w C.output u := by
    change ((C.gates ++ tail (26+C.gates.length) C.output u).foldl push (List.ofFn x)) = _
    rw [List.foldl_append]
    change (tail (26+C.gates.length) C.output u).foldl push w = _
    rw [← hw]
    exact tail_run w C.output u (by rw [hw]; omega) (by rwa [hw]) (by rwa [hw])
  have p0 : w.getD 0 false = x (Fin.castAdd 13 0) := wire_input C x (Fin.castAdd 13 0)
  have p1 : w.getD 1 false = x (Fin.castAdd 13 1) := wire_input C x (Fin.castAdd 13 1)
  have p3 : w.getD 3 false = x (Fin.castAdd 13 3) := wire_input C x (Fin.castAdd 13 3)
  have p9 : w.getD 9 false = x (Fin.castAdd 13 9) := wire_input C x (Fin.castAdd 13 9)
  have l0 : w.getD 13 false = x 13 := wire_input C x 13
  have p := any_point (fun i => x (Fin.castAdd 13 i))
  have m := any_point (fun i => x (Fin.castAdd 13 i) && wireValue C 26 x (u i))
  simp only [Bool.and_eq_true] at m
  rw [p, m]
  simp only [PEqualNP.BlindGate.wireValue, combined, ← hw, read_new, tail_bits,
    List.getD_cons_zero, List.getD_cons_succ, p0, p1, p3, p9, l0]
  <;> constructor <;> rfl

theorem final_gate (C : Circuit) (u : Fin 13 → ℕ) :
    (extend C u).gates[C.gates.length+13]? =
      some (gate .and (26+C.gates.length+3) (26+C.gates.length+12)) := by
  change (C.gates ++ tail (26+C.gates.length) C.output u)[C.gates.length+13]? = _
  rw [List.getElem?_append_right (by omega)]
  simp [tail]

end PEqualNP.Outside.L_meta_18543

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Outside.L_meta_18543 in
theorem PEqualNP.Outside.L_meta_18543 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →     (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →       x1.output < (26 : ℕ) + x1.size →         (∀ x6 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x6 < (26 : ℕ) + x1.size ∧ x2 x6 ≠ ↑x6) →           ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) (x9 : ℕ) (x10 : ℕ),             x7.size ≤ x1.size + (14 : ℕ) ∧               PEqualNP.TopForm.IsAO2 (26 : ℕ) x7 ∧                 (∀ x11 ∈ x7.gates, x11.inputs.Nodup) ∧                   x7.output = (26 : ℕ) + x8 ∧                     x7.gates[x8]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9, x10] : PEqualNP.CircuitLowerBounds.Gate } ∧                       ∀ (x11 : Fin (26 : ℕ) → Bool),                         have x12 : Bool := Decidable.decide (∃ x12 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true);                         have x13 : Bool := Decidable.decide (∃ x13 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x11 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 (x2 x13) = Bool.true);                         have x14 : Bool := x1.eval (List.ofFn x11);                         PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x9 = (x14 || x12) ∧ PEqualNP.BlindGate.wireValue x7 (26 : ℕ) x11 x10 = (x14 || x13 || x11 (13 : Fin (26 : ℕ))) := by
  intro C u hC hd ho hu
  have ho' : C.output < 26+C.gates.length := ho
  have hu' : ∀ p ∈ PEqualNP.HeptadCover.singerLines3 0, u p < 26+C.gates.length ∧
      u p ≠ p.val := hu
  obtain ⟨hmodel, hnodup⟩ := extend_good C u hC hd ho' hu'
  refine ⟨extend C u, C.gates.length+13, 26+C.gates.length+3, 26+C.gates.length+12,
    ?_, hmodel, hnodup, by simp [extend, Nat.add_assoc], final_gate C u, ?_⟩
  · simp [Circuit.size, extend, tail]
  · intro x
    exact operand_values C u ho' (fun p hp => (hu' p hp).1) x
