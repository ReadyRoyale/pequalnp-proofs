import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20132_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 8]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [12, 28]⟩, ⟨.or, [22, 26]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [19, 24]⟩, ⟨.or, [8, 30]⟩, ⟨.or, [14, 32]⟩, ⟨.and, [36, 31]⟩, ⟨.and, [23, 29]⟩, ⟨.and, [27, 25]⟩, ⟨.and, [34, 33]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 41]⟩, ⟨.or, [45, 42]⟩], 46⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20132_aux

theorem PEqualNP.Outside.L_meta_20132 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11770628888104126035 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20132_aux.main
