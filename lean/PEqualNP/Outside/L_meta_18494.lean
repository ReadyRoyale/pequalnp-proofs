import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18494

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Input := Fin 10 → Bool

def decode (m : Nat) (i : Fin 10) : Bool := m.testBit i.val

def zeroSel (m : Nat) : Input := Function.update (decode m) 0 false

def chosen (q : Nat → Bool) (m : Nat) : Input := Function.update (decode m) 0 (m.testBit 0 && q m)

def target (x : Input) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def positive : List Nat := [3,6,12,17,24,33,66,132,160,264,288,320,528,576,640]
def negative : List Nat := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]

def below (x y : Input) : Bool := (List.finRange 10).all fun i => !x i || y i

lemma belowValid {x y : Input} (h : below x y = true) : x ≤ y := by
  intro i
  have h' := List.all_eq_true.mp h i (List.mem_finRange i)
  change (!x i || y i) = true at h'
  cases hx : x i <;> cases hy : y i <;> simp [hx,hy] at h' ⊢

def lower (L : List ℕ) (x : Input) : Bool := L.any fun m => below (decode m) x
def upper (L : List ℕ) (x : Input) : Bool := L.any fun m => below x (zeroSel m)

lemma lowerWitness {L : List ℕ} {x : Input} (h : lower L x = true) :
    ∃ m ∈ L, decode m ≤ x := by
  obtain ⟨m,hm,q⟩ := List.any_eq_true.mp h
  exact ⟨m,hm,belowValid q⟩

lemma upperWitness {L : List ℕ} {x : Input} (h : upper L x = true) :
    ∃ m ∈ L, x ≤ zeroSel m := by
  obtain ⟨m,hm,q⟩ := List.any_eq_true.mp h
  exact ⟨m,hm,belowValid q⟩

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma trueBoundary : ∀ x : Input, x 0 = false → target x = true →
    lower (positive.filter fun m => !m.testBit 0) x = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma falseBoundary : ∀ x : Input, x 0 = false → target x = false → upper negative x = true := by
  decide +kernel

lemma chosenEven (q : Nat → Bool) {m : Nat} (even : m.testBit 0 = false) : chosen q m = decode m := by
  funext i
  by_cases h : i = 0
  · subst i
    simp [chosen, decode, even]
  · simp [chosen, Function.update_of_ne h]

lemma chosenAbove (q : Nat → Bool) (m : Nat) : zeroSel m ≤ chosen q m := by
  intro i
  by_cases h : i = 0
  · subst i
    simp [zeroSel, chosen]
  · simp [zeroSel, chosen, Function.update_of_ne h]

lemma readInput {n : Nat} (x : Fin n → Bool) (i : Nat) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i,h⟩ := by
  simp [List.getD_eq_getElem?_getD,h]

lemma evalUp (C : Circuit) (mono : Monotone2 C) {x y : Input} (le : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (mono g hg).1
  apply wiresFrom_mono C.gates ops _ _ (by simp) _ C.output
  intro i h
  by_cases hi : i < 10
  · rw [readInput _ _ hi] at h ⊢
    have less := le ⟨i,hi⟩
    rw [h] at less
    cases b : y ⟨i,hi⟩ with
    | false => exact ((show ¬ ((true : Bool) ≤ false) by decide) (b ▸ less)).elim
    | true => rfl
  · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at h
    exact Bool.noConfusion h

lemma main (C : Circuit) (q : Nat → Bool) (mono : Monotone2 C)
    (pos : ∀ m ∈ positive, C.eval (List.ofFn (chosen q m)) = true)
    (neg : ∀ m ∈ negative, C.eval (List.ofFn (chosen q m)) = false)
    (x : Input) (zero : x 0 = false) : C.eval (List.ofFn x) = target x := by
  cases e : target x with
  | false =>
    obtain ⟨m,hm,hxy⟩ := upperWitness (falseBoundary x zero e)
    apply Bool.eq_false_iff.mpr
    intro yes
    have contra := evalUp C mono (hxy.trans (chosenAbove q m)) yes
    rw [neg m hm] at contra
    exact Bool.noConfusion contra
  | true =>
    obtain ⟨m,hm,hxy⟩ := lowerWitness (trueBoundary x zero e)
    obtain ⟨hm,bit⟩ := List.mem_filter.mp hm
    have even : m.testBit 0 = false := by simpa using bit
    exact evalUp C mono hxy (by simpa only [chosenEven q even] using pos m hm)

end PEqualNP.Outside.L_meta_18494

theorem PEqualNP.Outside.L_meta_18494 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ → Bool), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x1.eval (List.ofFn (Function.update (fun (x6 : Fin (10 : ℕ)) => x4.testBit ↑x6) (0 : Fin (10 : ℕ)) (x4.testBit (0 : ℕ) && x2 x4))) = Bool.true) → (∀ x5 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x1.eval (List.ofFn (Function.update (fun (x7 : Fin (10 : ℕ)) => x5.testBit ↑x7) (0 : Fin (10 : ℕ)) (x5.testBit (0 : ℕ) && x2 x5))) = Bool.false) → ∀ (x6 : Fin (10 : ℕ) → Bool), x6 (0 : Fin (10 : ℕ)) = Bool.false → x1.eval (List.ofFn x6) = (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 :=
  PEqualNP.Outside.L_meta_18494.main
