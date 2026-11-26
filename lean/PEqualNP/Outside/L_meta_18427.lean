import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18427_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Test := List Bool → Bool

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def value (gs : List Gate) (x : List Bool) (i : ℕ) : Bool :=
  (gs.foldl step x).getD i false

theorem fold_prefix (gs : List Gate) (x : List Bool) :
    ∃ tail, gs.foldl step x = x ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[],by simp⟩
  | cons g rest ih =>
    obtain ⟨tail,ht,hl⟩ := ih (step x g)
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: tail,?_ ,by simp [hl]⟩
    rw [List.foldl_cons,ht]
    simp [step]

theorem fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  obtain ⟨tail,ht,hl⟩ := fold_prefix gs x
  rw [ht,List.length_append,hl]

theorem fold_read (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  obtain ⟨_,ht,_⟩ := fold_prefix gs x
  rw [ht,List.getD_append _ _ _ _ hi]

def Valid (gs : List Gate) : Prop := Monotone2 ⟨gs,0⟩

structure Ext (gs hs : List Gate) (k : ℕ) : Prop where
  appended : ∃ tail, hs = gs ++ tail
  size : hs.length ≤ gs.length + k
  valid : Valid hs

theorem Ext.same {gs : List Gate} (h : Valid gs) : Ext gs gs 0 :=
  ⟨⟨[],by simp⟩,by simp,h⟩

theorem Ext.trans {a b c : List Gate} {k l : ℕ} (ab : Ext a b k) (bc : Ext b c l) :
    Ext a c (k+l) := by
  obtain ⟨tail,ht⟩ := ab.appended
  obtain ⟨more,hm⟩ := bc.appended
  exact ⟨⟨tail++more,by rw [hm,ht,List.append_assoc]⟩,by have := ab.size; have := bc.size; omega,bc.valid⟩

def Wire (n : ℕ) (gs : List Gate) (i : ℕ) (f : Test) : Prop :=
  i < n + gs.length ∧ ∀ x : List Bool, x.length = n → value gs x i = f x

theorem Wire.with_test {n i : ℕ} {gs : List Gate} {f g : Test} (w : Wire n gs i f)
    (same : ∀ x, f x = g x) : Wire n gs i g :=
  ⟨w.1,fun x hx => (w.2 x hx).trans (same x)⟩

theorem Ext.keep {n i k : ℕ} {a b : List Gate} {f : Test} (h : Ext a b k) (w : Wire n a i f) :
    Wire n b i f := by
  obtain ⟨tail,rfl⟩ := h.appended
  refine ⟨by simp; have := w.1; omega,?_⟩
  intro x hx
  simp only [value,List.foldl_append]
  rw [fold_read tail _ i (by rw [fold_length,hx]; exact w.1)]
  exact w.2 x hx

theorem input_wire {n i : ℕ} (gs : List Gate) (h : i < n) :
    Wire n gs i (fun x => x.getD i false) := by
  exact ⟨by omega,fun x hx => fold_read gs x i (hx.symm ▸ h)⟩

theorem binary {n a b : ℕ} {gs : List Gate} {f g : Test}
    (orGate : Bool) (ok : Valid gs) (wa : Wire n gs a f) (wb : Wire n gs b g) :
    ∃ hs i, Ext gs hs 1 ∧ Wire n hs i (fun x => if orGate then f x || g x else f x && g x) := by
  let t : Gate := ⟨if orGate then .or else .and,[a,b]⟩
  let hs := gs ++ [t]
  refine ⟨hs,n+gs.length,⟨⟨[t],rfl⟩,by simp [hs],?_⟩,by simp [hs],?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with old | newGate
    · exact ok j old
    · have eq := List.mem_singleton.mp newGate
      subst j
      cases orGate <;> simp [t]
  · intro x hx
    have ln : (gs.foldl step x).length = n+gs.length := by rw [fold_length,hx]
    change ((hs.foldl step x).getD (n+gs.length) false) =
      (if orGate then f x || g x else f x && g x)
    simp only [hs,List.foldl_append,List.foldl_cons,List.foldl_nil,step]
    rw [← ln,List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self,List.getD_cons_zero]
    change t.op.eval [value gs x a,value gs x b] = (if orGate then f x || g x else f x && g x)
    rw [wa.2 x hx,wb.2 x hx]
    cases orGate <;> simp [t,GateOp.eval]

def anyOn (fs : List Test) (x : List Bool) : Bool := fs.any (fun f => f x)

def two : List Bool → Bool
  | [] => false
  | a::tail => (a && tail.any id) || two tail

def twoOn (fs : List Test) (x : List Bool) : Bool := two (fs.map (fun f => f x))

theorem wire_any (n : ℕ) (fs : List Test) (gs : List Gate) (ok : Valid gs) (ne : fs ≠ [])
    (source : ∀ f ∈ fs, ∃ i, Wire n gs i f) :
    ∃ hs i, Ext gs hs (fs.length - 1) ∧ Wire n hs i (anyOn fs) := by
  induction fs generalizing gs with
  | nil => contradiction
  | cons f tail ih =>
    obtain ⟨a,wa⟩ := source f (by simp)
    cases tail with
    | nil => exact ⟨gs,a,by simpa using Ext.same ok,wa.with_test (fun _ => by simp [anyOn])⟩
    | cons g rest =>
      obtain ⟨hs,b,ext,wb⟩ := ih gs ok (by simp)
        (fun v hv => source v (List.mem_cons_of_mem _ hv))
      obtain ⟨ks,i,move,wi⟩ := binary true ext.valid (ext.keep wa) wb
      refine ⟨ks,i,?_ ,?_⟩
      · simpa using ext.trans move
      · exact wi.with_test (fun _ => by simp [anyOn])

theorem wires_two_and_any (n : ℕ) (fs : List Test) (gs : List Gate) (ok : Valid gs)
    (large : 2 ≤ fs.length) (source : ∀ f ∈ fs, ∃ i, Wire n gs i f) :
    ∃ hs i a, Ext gs hs (3*fs.length-4) ∧ Wire n hs i (twoOn fs) ∧ Wire n hs a (anyOn fs) := by
  induction fs generalizing gs with
  | nil => simp at large
  | cons f tail ih =>
    obtain ⟨a,wa⟩ := source f (by simp)
    cases tail with
    | nil => simp at large
    | cons g rest =>
      by_cases none : rest = []
      · subst rest
        obtain ⟨b,wb⟩ := source g (by simp)
        obtain ⟨g1,t,e1,wt⟩ := binary false ok wa wb
        obtain ⟨g2,o,e2,wo⟩ := binary true e1.valid (e1.keep wa) (e1.keep wb)
        exact ⟨g2,t,o,by simpa using e1.trans e2,
          (e2.keep wt).with_test (fun _ => by simp [twoOn,two]),wo.with_test (fun _ => by simp [anyOn])⟩
      · have big : 2 ≤ (g::rest).length := by
          have nz := List.length_pos_iff.mpr none
          simp only [List.length_cons]
          omega
        obtain ⟨g1,t,b,e1,wt,wb⟩ := ih gs ok big
          (fun v hv => source v (List.mem_cons_of_mem _ hv))
        obtain ⟨g2,c,e2,wc⟩ := binary false e1.valid (e1.keep wa) wb
        obtain ⟨g3,z,e3,wz⟩ := binary true e2.valid wc (e2.keep wt)
        obtain ⟨g4,o,e4,wo⟩ := binary true e3.valid (e3.keep (e2.keep (e1.keep wa))) (e3.keep (e2.keep wb))
        have full := (((e1.trans e2).trans e3).trans e4)
        have count : 3 * (g::rest).length - 4 + 1 + 1 + 1 = 3 * (f::g::rest).length - 4 := by
          simp only [List.length_cons] at big ⊢
          omega
        exact ⟨g4,z,o,count ▸ full,
          (e4.keep wz).with_test (fun _ => by simp [twoOn,two,anyOn,List.any_map]),
          wo.with_test (fun _ => by simp [anyOn])⟩

theorem wire_two (n : ℕ) (fs : List Test) (gs : List Gate) (ok : Valid gs)
    (large : 2 ≤ fs.length) (source : ∀ f ∈ fs, ∃ i, Wire n gs i f) :
    ∃ hs i, Ext gs hs (3*fs.length-5) ∧ Wire n hs i (twoOn fs) := by
  cases fs with
  | nil => simp at large
  | cons f tail =>
    cases tail with
    | nil => simp at large
    | cons g rest =>
      obtain ⟨a,wa⟩ := source f (by simp)
      by_cases none : rest = []
      · subst rest
        obtain ⟨b,wb⟩ := source g (by simp)
        obtain ⟨hs,j,move,wire⟩ := binary false ok wa wb
        exact ⟨hs,j,by simpa using move,wire.with_test (fun _ => by simp [twoOn,two])⟩
      · have many : 2 ≤ (g::rest).length := by
          have pp := List.length_pos_iff.mpr none
          simp only [List.length_cons]
          omega
        obtain ⟨g1,t,b,e1,wt,wb⟩ := wires_two_and_any n (g::rest) gs ok many
          (fun v hv => source v (List.mem_cons_of_mem _ hv))
        obtain ⟨g2,c,e2,wc⟩ := binary false e1.valid (e1.keep wa) wb
        obtain ⟨g3,z,e3,wz⟩ := binary true e2.valid wc (e2.keep wt)
        have exactCost : 3*(g::rest).length-4 + 1 + 1 = 3*(f::g::rest).length-5 := by
          simp only [List.length_cons] at many ⊢
          omega
        exact ⟨g3,z,exactCost ▸ (e1.trans e2).trans e3,
          wz.with_test (fun _ => by simp [twoOn,two,anyOn,List.any_map])⟩

theorem batch {α : Type} (n : ℕ) (base : List Gate) (valid : Valid base)
    (jobs : List α) (cost : α → ℕ) (target : α → Test)
    (make : ∀ j ∈ jobs, ∀ gs k, Ext base gs k →
      ∃ hs i, Ext gs hs (cost j) ∧ Wire n hs i (target j)) :
    ∃ gs, Ext base gs (jobs.map cost).sum ∧ ∀ j ∈ jobs, ∃ i, Wire n gs i (target j) := by
  induction jobs with
  | nil => exact ⟨base,Ext.same valid,by simp⟩
  | cons j tail ih =>
    obtain ⟨gs,step,old⟩ := ih (fun v hv => make v (List.mem_cons_of_mem _ hv))
    obtain ⟨hs,i,move,wire⟩ := make j (by simp) gs _ step
    refine ⟨hs,by simpa [Nat.add_comm] using step.trans move,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | mem
    · exact ⟨i,wire⟩
    · obtain ⟨w,hw⟩ := old f mem
      exact ⟨w,move.keep hw⟩

end PEqualNP.Outside.L_meta_18427_aux
namespace PEqualNP.Outside.L_meta_18427_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def fused (n i : ℕ) (x : List Bool) : Bool := x.getD i false || x.getD (n+i) false

def rowCells (n c i : ℕ) : List Test := (List.range c).map (fun j => fused n (i*c+j))
def colCells (n r c j : ℕ) : List Test := (List.range r).map (fun i => fused n (i*c+j))
def rowTerms (n r c : ℕ) : List Test := (List.range r).map (fun i => anyOn (rowCells n c i))
def colTerms (n r c : ℕ) : List Test := (List.range c).map (fun j => anyOn (colCells n r c j))

def wanted (r c : ℕ) (x : List Bool) : Bool :=
  let n := r*c+1
  (twoOn (rowTerms n r c) x || twoOn (colTerms n r c) x) ||
    (fused n (r*c) x && anyOn (rowTerms n r c) x)

theorem cell_bound {i j r c : ℕ} (hi : i < r) (hj : j < c) : i * c + j < r * c := by
  have h := Nat.mul_le_mul_right c (show i+1 ≤ r by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

theorem constant_jobs (n k : ℕ) : ((List.range n).map (fun _ => k)).sum = n*k := by
  simp [List.map_const']

theorem implementation (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    ∃ gs w, Valid gs ∧ gs.length ≤ 3*(r*c+1)+2*(r+c)-8 ∧
      Wire ((r*c+1)+(r*c+1)) gs w (wanted r c) := by
  let n := r*c+1
  let N := n+n
  have empty : Valid [] := by simp [Valid,Monotone2]
  have makeFused (i : ℕ) (hi : i ∈ List.range n) (gs : List Gate) (k : ℕ) (E : Ext [] gs k) :
      ∃ hs w, Ext gs hs 1 ∧ Wire N hs w (fused n i) := by
    have b := List.mem_range.mp hi
    have first : i < N := by dsimp [N]; omega
    have second : n+i < N := by dsimp [N]; omega
    exact binary true E.valid (input_wire gs first) (input_wire gs second)
  obtain ⟨gs,E,merged⟩ := batch N [] empty (List.range n) (fun _ => 1) (fused n) makeFused
  have row i (hi : i ∈ List.range r) (hs : List Gate) (k : ℕ) (extend : Ext gs hs k) :
      ∃ ks w, Ext hs ks (c-1) ∧ Wire N ks w (anyOn (rowCells n c i)) := by
    have len : (rowCells n c i).length = c := by simp [rowCells]
    have nonempty : rowCells n c i ≠ [] := by intro e; rw [e] at len; simp at len; omega
    obtain ⟨ks,w,E',sol⟩ := wire_any N (rowCells n c i) hs extend.valid nonempty (by
      intro f hf
      obtain ⟨j,jMem,rfl⟩ := List.mem_map.mp hf
      have bound := cell_bound (List.mem_range.mp hi) (List.mem_range.mp jMem)
      have m : i*c+j ∈ List.range n := List.mem_range.mpr (by dsimp [n]; omega)
      obtain ⟨b,wb⟩ := merged _ m
      exact ⟨b,extend.keep wb⟩)
    exact ⟨ks,w,by simpa only [len] using E',sol⟩
  obtain ⟨hs,Erow,rows⟩ := batch N gs E.valid (List.range r) (fun _ => c-1)
    (fun i => anyOn (rowCells n c i)) row
  have column j (hj : j ∈ List.range c) (ks : List Gate) (k : ℕ) (extend : Ext hs ks k) :
      ∃ ls w, Ext ks ls (r-1) ∧ Wire N ls w (anyOn (colCells n r c j)) := by
    have len : (colCells n r c j).length = r := by simp [colCells]
    have nonempty : colCells n r c j ≠ [] := by intro e; rw [e] at len; simp at len; omega
    obtain ⟨ls,w,E',sol⟩ := wire_any N (colCells n r c j) ks extend.valid nonempty (by
      intro f hf
      obtain ⟨i,iMem,rfl⟩ := List.mem_map.mp hf
      have bound := cell_bound (List.mem_range.mp iMem) (List.mem_range.mp hj)
      have m : i*c+j ∈ List.range n := List.mem_range.mpr (by dsimp [n]; omega)
      obtain ⟨b,wb⟩ := merged _ m
      exact ⟨b,extend.keep (Erow.keep wb)⟩)
    exact ⟨ls,w,by simpa only [len] using E',sol⟩
  obtain ⟨ks,Ecol,cols⟩ := batch N hs Erow.valid (List.range c) (fun _ => r-1)
    (fun j => anyOn (colCells n r c j)) column
  have rLen : (rowTerms n r c).length = r := by simp [rowTerms]
  have cLen : (colTerms n r c).length = c := by simp [colTerms]
  obtain ⟨l1,wr,wa,Ert,rWire,aWire⟩ := wires_two_and_any N (rowTerms n r c) ks Ecol.valid
    (by simpa [rLen] using hr) (by
      intro f hf
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
      obtain ⟨k,kWire⟩ := rows i hi
      exact ⟨k,Ecol.keep kWire⟩)
  obtain ⟨l2,wc,Ect,cWire⟩ := wire_two N (colTerms n r c) l1 Ert.valid
    (by simpa [cLen] using hc) (by
      intro f hf
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hf
      obtain ⟨k,kWire⟩ := cols i hi
      exact ⟨k,Ert.keep kWire⟩)
  obtain ⟨special,sWire⟩ := merged (r*c) (List.mem_range.mpr (by simp [n]))
  obtain ⟨l3,ws,Eextra,extraWire⟩ := binary false Ect.valid
    (Ect.keep (Ert.keep (Ecol.keep (Erow.keep sWire)))) (Ect.keep aWire)
  obtain ⟨l4,wo,Ej,joinWire⟩ := binary true Eextra.valid (Eextra.keep (Ect.keep rWire)) (Eextra.keep cWire)
  obtain ⟨l5,wf,Eout,final⟩ := binary true Ej.valid joinWire (Ej.keep extraWire)
  have allMoves := (((((((E.trans Erow).trans Ecol).trans Ert).trans Ect).trans Eextra).trans Ej).trans Eout)
  have acc := allMoves.size
  have a₁ : r ≤ r*c := by
    simpa using Nat.mul_le_mul_left r (show 1 ≤ c by omega)
  have a₂ : c ≤ r*c := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left c (show 1 ≤ r by omega)
  rw [constant_jobs,constant_jobs,constant_jobs,rLen,cLen,Nat.mul_sub_left_distrib,
    Nat.mul_sub_left_distrib,Nat.mul_one,Nat.mul_one,Nat.mul_one] at acc
  rw [Nat.mul_comm c r] at acc
  refine ⟨l5,wf,Eout.valid,by simp [n] at acc; omega,?_⟩
  exact final

end PEqualNP.Outside.L_meta_18427_aux
namespace PEqualNP.Outside.L_meta_18427_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem two_spec (xs : List Bool) :
    two xs = true ↔ ∃ i j : ℕ, i < j ∧ j < xs.length ∧ xs.getD i false = true ∧
      xs.getD j false = true := by
  induction xs with
  | nil => simp [two]
  | cons b rest ih =>
    simp only [two,Bool.or_eq_true,Bool.and_eq_true,ih,List.length_cons]
    constructor
    · rintro (⟨hb,tail⟩ | ⟨i,j,lt,range,x,y⟩)
      · obtain ⟨t,ht,bt⟩ := List.any_eq_true.mp tail
        have tTrue : t = true := bt
        have tm : true ∈ rest := by simpa only [tTrue] using ht
        obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp tm
        have atK : rest.getD k false = true := by
          rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,eq]; rfl
        exact ⟨0,k+1,by omega,by omega,by simpa using hb,by simpa using atK⟩
      · exact ⟨i+1,j+1,by omega,by omega,by simpa using x,by simpa using y⟩
    · rintro ⟨i,j,lt,range,x,y⟩
      cases j with
      | zero => omega
      | succ j =>
        have hj : j < rest.length := by omega
        cases i with
        | zero =>
          refine Or.inl ⟨by simpa using x,?_⟩
          have atJ : rest[j]'hj = true := by
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using
              (show rest.getD j false = true from y)
          exact List.any_eq_true.mpr ⟨true,atJ ▸ List.getElem_mem hj,rfl⟩
        | succ i =>
          exact Or.inr ⟨i,j,by omega,hj,by simpa using x,by simpa using y⟩

theorem range_getD (n : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD,hi]

theorem two_range (n : ℕ) (f : ℕ → Bool) :
    two ((List.range n).map f) = true ↔
      ∃ i < n, ∃ j < n, i ≠ j ∧ f i = true ∧ f j = true := by
  rw [two_spec]
  simp only [List.length_map,List.length_range]
  constructor
  · rintro ⟨i,j,order,jr,a,b⟩
    have ir : i < n := order.trans jr
    exact ⟨i,ir,j,jr,ne_of_lt order,by simpa only [range_getD n f i ir] using a,
      by simpa only [range_getD n f j jr] using b⟩
  · rintro ⟨i,ir,j,jr,ne,a,b⟩
    rw [← range_getD n f i ir] at a
    rw [← range_getD n f j jr] at b
    rcases lt_or_gt_of_ne ne with order | order
    · exact ⟨i,j,order,jr,a,b⟩
    · exact ⟨j,i,order,ir,b,a⟩

theorem two_buckets (n a b : ℕ) (f : ℕ → Bool) (P Q : Prop)
    (pa : P → a < n) (qb : Q → b < n)
    (values : ∀ i < n, f i = true ↔ (P ∧ i=a) ∨ (Q ∧ i=b)) :
    two ((List.range n).map f) = true ↔ P ∧ Q ∧ a ≠ b := by
  rw [two_range]
  constructor
  · rintro ⟨i,hi,j,hj,d,fi,fj⟩
    have a1 := (values i hi).mp fi
    have a2 := (values j hj).mp fj
    rcases a1 with ⟨h,rfl⟩ | ⟨h,rfl⟩ <;>
      rcases a2 with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · exact (d rfl).elim
    · exact ⟨h,k,d⟩
    · exact ⟨k,h,d.symm⟩
    · exact (d rfl).elim
  · rintro ⟨p,q,d⟩
    exact ⟨a,pa p,b,qb q,d,(values a (pa p)).mpr (Or.inl ⟨p,rfl⟩),
      (values b (qb q)).mpr (Or.inr ⟨q,rfl⟩)⟩

theorem fused_one {n i : ℕ} (u v : Fin n) (hi : i < n) :
    fused n i (oneEach u v) = true ↔ i = u.val ∨ i = v.val := by
  let l := List.ofFn (fun j : Fin n => decide (j = u))
  let rr := List.ofFn (fun j : Fin n => decide (j = v))
  have ll : l.length = n := by simp [l]
  have rrL : rr.length = n := by simp [rr]
  have atL : l.getD i false = decide (i = u.val) := by
    simp [l,List.getD_eq_getElem?_getD,hi,Fin.ext_iff]
  have atR : rr.getD i false = decide (i = v.val) := by
    simp [rr,List.getD_eq_getElem?_getD,hi,Fin.ext_iff]
  change ((l++rr).getD i false || (l++rr).getD (n+i) false) = true ↔ _
  rw [List.getD_append _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),ll,
    show n+i-n=i by omega,atL,atR]
  simp

theorem row_position {r c i a : ℕ} (hi : i < r) (cp : 0 < c) :
    (∃ j < c, i*c+j=a) ↔ a < r*c ∧ a / c = i := by
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨cell_bound hi hj,?_⟩
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ cp, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rintro ⟨_,h⟩
    exact ⟨a % c,Nat.mod_lt _ cp,by rw [← h,Nat.div_add_mod']⟩

theorem column_position {r c j a : ℕ} (hj : j < c) (cp : 0 < c) :
    (∃ i < r, i*c+j=a) ↔ a < r*c ∧ a % c = j := by
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨cell_bound hi hj,Nat.mul_add_mod_of_lt hj⟩
  · rintro ⟨ha,h⟩
    exact ⟨a / c,(Nat.div_lt_iff_lt_mul cp).mpr ha,by rw [← h,Nat.div_add_mod']⟩

theorem cell_or_occupied {k n : ℕ} (u v : Fin n) (cells : ℕ → ℕ)
    (range : ∀ j < k, cells j < n) :
    anyOn ((List.range k).map fun j => fused n (cells j)) (oneEach u v) = true ↔
      (∃ j < k, cells j = u.val) ∨ ∃ j < k, cells j = v.val := by
  unfold anyOn
  rw [List.any_map,List.any_eq_true]
  constructor
  · rintro ⟨j,hj,f⟩
    have jk := List.mem_range.mp hj
    rcases (fused_one u v (range j jk)).mp f with h | h
    · exact Or.inl ⟨j,jk,h⟩
    · exact Or.inr ⟨j,jk,h⟩
  · rintro (⟨j,hj,e⟩ | ⟨j,hj,e⟩)
    · exact ⟨j,List.mem_range.mpr hj,(fused_one u v (range j hj)).mpr (Or.inl e)⟩
    · exact ⟨j,List.mem_range.mpr hj,(fused_one u v (range j hj)).mpr (Or.inr e)⟩

theorem row_hit {r c i : ℕ} (cp : 0 < c) (hi : i < r) (u v : Fin (r*c+1)) :
    anyOn (rowCells (r*c+1) c i) (oneEach u v) = true ↔
      (u.val < r*c ∧ u.val / c = i) ∨ (v.val < r*c ∧ v.val / c = i) := by
  unfold rowCells
  rw [cell_or_occupied u v _ (fun j hj => (cell_bound hi hj).trans (Nat.lt_succ_self _)),
    row_position hi cp,row_position hi cp]

theorem col_hit {r c j : ℕ} (cp : 0 < c) (hj : j < c) (u v : Fin (r*c+1)) :
    anyOn (colCells (r*c+1) r c j) (oneEach u v) = true ↔
      (u.val < r*c ∧ u.val % c = j) ∨ (v.val < r*c ∧ v.val % c = j) := by
  unfold colCells
  rw [cell_or_occupied u v _ (fun i hi => (cell_bound hi hj).trans (Nat.lt_succ_self _)),
    column_position hj cp,column_position hj cp]

theorem some_row {r c : ℕ} (cp : 0 < c) (u v : Fin (r*c+1)) :
    anyOn (rowTerms (r*c+1) r c) (oneEach u v) = true ↔ u.val < r*c ∨ v.val < r*c := by
  unfold rowTerms anyOn
  rw [List.any_map,List.any_eq_true]
  constructor
  · rintro ⟨i,hi,h⟩
    rcases (row_hit cp (List.mem_range.mp hi) u v).mp h with a | b
    · exact Or.inl a.1
    · exact Or.inr b.1
  · rintro (hu | hv)
    · have urow := (Nat.div_lt_iff_lt_mul cp).mpr hu
      exact ⟨u.val / c,List.mem_range.mpr urow,(row_hit cp urow u v).mpr (Or.inl ⟨hu,rfl⟩)⟩
    · have vrow := (Nat.div_lt_iff_lt_mul cp).mpr hv
      exact ⟨v.val / c,List.mem_range.mpr vrow,(row_hit cp vrow u v).mpr (Or.inr ⟨hv,rfl⟩)⟩

theorem wanted_correct {r c : ℕ} (cp : 0 < c) (u v : Fin (r*c+1)) :
    wanted r c (oneEach u v) = true ↔ u ≠ v := by
  have rows : twoOn (rowTerms (r*c+1) r c) (oneEach u v) = true ↔
      u.val < r*c ∧ v.val < r*c ∧ u.val / c ≠ v.val / c := by
    unfold twoOn rowTerms
    rw [List.map_map]
    exact two_buckets r (u.val / c) (v.val / c) _
      (u.val < r*c) (v.val < r*c) ((Nat.div_lt_iff_lt_mul cp).mpr) ((Nat.div_lt_iff_lt_mul cp).mpr)
      (fun i hi => by simpa only [Function.comp_apply,eq_comm] using row_hit cp hi u v)
  have cols : twoOn (colTerms (r*c+1) r c) (oneEach u v) = true ↔
      u.val < r*c ∧ v.val < r*c ∧ u.val % c ≠ v.val % c := by
    unfold twoOn colTerms
    rw [List.map_map]
    exact two_buckets c (u.val % c) (v.val % c) _
      (u.val < r*c) (v.val < r*c) (fun _ => Nat.mod_lt _ cp) (fun _ => Nat.mod_lt _ cp)
      (fun i hi => by simpa only [Function.comp_apply,eq_comm] using col_hit cp hi u v)
  have special := fused_one u v (i := r*c) (Nat.lt_succ_self _)
  simp only [wanted,Bool.or_eq_true,Bool.and_eq_true,rows,cols,special,some_row cp]
  constructor
  · rintro ((⟨h₁,h₂,d⟩ | ⟨h₁,h₂,d⟩) | ⟨h,h'⟩)
    · rintro rfl; exact d rfl
    · rintro rfl; exact d rfl
    · rintro rfl
      rcases h with eq | eq <;> rcases h' with lt | lt <;> omega
  · intro diff
    have x := u.isLt
    have y := v.isLt
    by_cases baseU : u.val < r*c <;> by_cases baseV : v.val < r*c
    · by_cases rowEq : u.val / c = v.val / c
      · refine Or.inl (Or.inr ⟨baseU,baseV,?_⟩)
        intro modEq
        apply diff
        apply Fin.ext
        calc
          u.val = u.val / c*c + u.val % c := (Nat.div_add_mod' _ _).symm
          _ = v.val / c*c + v.val % c := by rw [rowEq,modEq]
          _ = v.val := Nat.div_add_mod' _ _
      · exact Or.inl (Or.inl ⟨baseU,baseV,rowEq⟩)
    · exact Or.inr ⟨Or.inr (by omega),Or.inl baseU⟩
    · exact Or.inr ⟨Or.inl (by omega),Or.inr baseV⟩
    · exact (diff (Fin.ext (by omega))).elim

theorem result (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    RepSizeAtMost (fun u v : Fin (r*c+1) => decide (u ≠ v)) (3*(r*c+1)+2*(r+c)-8) := by
  obtain ⟨gs,w,valid,cost,wire⟩ := implementation r c hr hc
  refine ⟨⟨gs,w⟩,valid,cost,?_⟩
  intro u v
  have equal := wire.2 (oneEach u v) (by simp [oneEach]; omega)
  change value gs (oneEach u v) w = decide (u ≠ v)
  rw [equal]
  exact Bool.eq_iff_iff.mpr ((wanted_correct (by omega : 0 < c) u v).trans (by simp))

end PEqualNP.Outside.L_meta_18427_aux

theorem PEqualNP.Outside.L_meta_18427 :
    ∀ r c : ℕ, 2 ≤ r → 2 ≤ c →
      PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (r * c + 1) => decide (u ≠ v))
        (3 * (r * c + 1) + 2 * (r + c) - 8) :=
  PEqualNP.Outside.L_meta_18427_aux.result