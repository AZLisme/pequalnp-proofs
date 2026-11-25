import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10718
namespace Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := Nat × Nat
def top : Nat := 0xffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def Valid1 (x : Nat) : Prop := ∀ j, 128 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma top_eq_pow : top = 2 ^ 64 * 2 ^ 64 - 1 := by decide
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 128) := by
  rw [top_eq_pow]; exact pow_add_testBit 64 64 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 128 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 128
  · simp [hj]
  · simp [hj, hx j (by omega)]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 128 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 128 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 64 * 2 ^ 64 := by
    have hp : 0 < 2 ^ 64 * 2 ^ 64 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 128 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 128 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
def bit (side : Bool) (i : Fin 128) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h; exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
end Basis1868


namespace Conflict1868
open Basis1868

abbrev I := Fin 128
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def D (p n : I) (a : Sig) : Prop := P a p ≠ N a n
def op (d x y : Bool) : Bool := if d then x || y else x && y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  by_contra! hn
  apply hd
  unfold P N
  rw [bop,bop]
  exact congrArg₂ (op d) (not_ne_iff.mp hn.1) (not_ne_iff.mp hn.2)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_neg {p n a} (hv : Valid a) : D p n (neg a) ↔ D p n a := by
  unfold D P N
  rw [bit_neg _ _ hv,bit_neg _ _ hv]
  cases bit true p a <;> cases bit false n a <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pair_sep {k t S} (hl : Live k t S) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,P,N,bit,target,testBit_top,p.isLt]
  | unary ha _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨_, Finset.mem_insert_self _ _, (d_neg ha.1).mp h⟩
    · exact ⟨_, Finset.mem_insert_of_mem hc, h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_unique_keep {p n a c U} (h : Unique p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Unique p n (insert (neg a) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · exact (hna (h _ (Finset.mem_insert_self _ _) ((d_neg hv).mp hd)).symm).elim
  · exact h _ (Finset.mem_insert_of_mem hu) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_keep {p n a c U} (h : Mark p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Mark p n (insert (neg a) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,neg_unique_keep hm hna hv⟩,q,neg_unique_keep hq hna hv⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_move {p n a U} (h : Mark p n (insert a U) a)
    (ha : a ∉ U) (hv : Valid a) : Mark p n (insert (neg a) U) (neg a) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a U := Finset.subset_insert _ _
  exact ⟨(d_neg hv).mpr hd,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mix : ∀ (d ap an bp bn al ar : Bool), ap ≠ an →
    op d ap bp ≠ op d al bp → op d ar bn ≠ op d an bn →
    bp = bn ∧ op d ap bp ≠ op d an bn := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U))
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : P b p = N b m := not_ne_iff.mp (fun h => hab (hm _ hb h).symm)
  have bq : P b q = N b n := not_ne_iff.mp (fun h => hab (hq _ hb h).symm)
  have zm := unique_diff tail (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  change bit true p (bin d a b) ≠ bit false m (bin d a b) at zm
  change bit true q (bin d a b) ≠ bit false n (bin d a b) at zq
  rw [bop,bop] at zm zq
  change op d (P a p) (P b p) ≠ op d (N a m) (N b m) at zm
  change op d (P a q) (P b q) ≠ op d (N a n) (N b n) at zq
  rw [← bm] at zm
  rw [bq] at zq
  have hh := mix _ _ _ _ _ _ _ hd zm zq
  refine ⟨fun h => h hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2


def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unary_col {k U a} (hv : Valid a) (fresh : neg a ∉ insert a U)
    (col : Colored (insert (neg a) U) k) :
    ∃ l, Colored (insert a U) l ∧ l + (insert a U).card ≤ k + (insert (neg a) U).card := by
  let R := ({a} : Finset Sig) ∩ U
  let f (x : Sig) := if x = a then neg a else x
  have mem (x) (hx : x ∈ insert a U) (_ : x ∉ R) : f x ∈ insert (neg a) U := by
    by_cases e : x = a
    · simp [f,e]
    · simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left e)
  have keep (x p n) (hxr : x ∉ R) (mx : Mark p n (insert a U) x) :
      Mark p n (insert (neg a) U) (f x) := by
    by_cases e : x = a
    · subst x
      have ha : a ∉ U := by simpa [R] using hxr
      simpa [f] using neg_mark_move mx ha hv
    · simpa [f,e] using neg_mark_keep mx e hv
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy hxr hyr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n hxr mx,keep y p n hyr my⟩
    by_cases ex : x = a <;> by_cases ey : y = a
    · exact (hxy (ex.trans ey.symm)).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : neg a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> simp [R,ha,Finset.card_insert_of_notMem] <;> omega

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
theorem live_colored {k t S} (l : Live k t S) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary ha hf _ ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := unary_col ha.1 hf hk
    exact ⟨u,hu,by omega⟩
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail hk
    exact ⟨u,hu,by omega⟩

end Conflict1868

namespace Grid1868
open Basis1868

abbrev Ix := Fin 256
def coord (side : Bool) (i : Nat) := if side then i / 16 * 16 else i % 16
def hop (n mask x : Nat) : Nat := (x ||| ((x <<< n) &&& (mask <<< n))) ||| ((x >>> n) &&& mask)
def safe (s : Bool) (n mask : Nat) : Prop :=
  ∀ i : Ix, (((mask <<< n).testBit i.val = true → n ≤ i.val ∧ coord s (i.val-n) = coord s i.val) ∧
    (mask.testBit i.val = true → i.val+n < 256 ∧ coord s (i.val+n) = coord s i.val))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
instance (s n m) : Decidable (safe s n m) := by unfold safe; infer_instance

def m4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def m5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def m6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def m7 : Nat := 0xffffffffffffffffffffffffffffffff
def col (x : Nat) := (hop 128 m7 (hop 64 m6 (hop 32 m5 (hop 16 m4 x))))
end Grid1868

namespace Check1868
open Basis1868
open Grid1868 Conflict1868

abbrev Signs := List (Sig × Nat)

end Check1868


namespace ColorSearch1868
open Basis1868
open Conflict1868 Check1868

def paint (n : Nat) : Signs → (Nat → Nat) → Bool
  | [], _ => true
  | x::xs, bins =>
    (List.range n).any fun i => ((bins i &&& x.2) == 0) &&
      paint n xs (fun j => if i=j then bins j ||| x.2 else bins j)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma paint_ok {n xs} (bins : Nat → Nat) (f : Sig → Nat) (nd : (xs.map Prod.fst).Nodup)
    (bd : ∀ x ∈ xs, f x.1 < n) (ok : ∀ x ∈ xs, bins (f x.1) &&& x.2 = 0)
    (sep : ∀ x ∈ xs, ∀ y ∈ xs, x.1 ≠ y.1 → f x.1 = f y.1 → x.2 &&& y.2 = 0) :
    paint n xs bins = true := by
  induction xs generalizing bins with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hn,hnd⟩ := List.nodup_cons.mp nd
    apply List.any_eq_true.mpr
    refine ⟨f x.1,List.mem_range.mpr (bd _ (by simp)),Bool.and_eq_true_iff.mpr ⟨by
      simp only [beq_iff_eq]; exact ok _ (by simp),?_⟩⟩
    apply ih _ hnd (fun a ha => bd a (List.mem_cons_of_mem _ ha)) _ (fun a ha b hb =>
      sep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    intro y hy
    have hy' := List.mem_cons_of_mem x hy
    by_cases e : f x.1 = f y.1
    · have ne : x.1 ≠ y.1 := fun eq => hn (List.mem_map.mpr ⟨y,hy,eq.symm⟩)
      simp [e,Nat.and_or_distrib_right,ok y hy',sep x (List.mem_cons_self ..) y hy' ne e]
    · simpa [e] using ok y hy'

end ColorSearch1868

namespace Free1868
open Basis1868
open Conflict1868

def flip (s : Bool) (a : Sig) := if s then neg a else a
def sign (a : Sig) := bit true 0 a
def can (a : Sig) := flip (sign a) a

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg2 (a : Sig) : neg (neg a) = a := by
  obtain ⟨u,v⟩ := a
  simp [neg,bnot,Nat.xor_assoc]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip2 (s a) : flip s (flip s a) = a := by cases s <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipFalse (a) : flip false a = a := rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma vf {a} (s) (h : Valid a) : Valid (flip s a) := by cases s <;> first | exact h | exact valid_neg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sign_neg {a} (h : Valid a) : sign (neg a) = !sign a := bit_neg true 0 h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_neg {a} (v : Valid a) : can (neg a) = can a := by
  unfold can
  rw [sign_neg v]
  cases sign a <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_flip {a} (s) (v : Valid a) : can (flip s a) = can a := by
  cases s with
  | false => rfl
  | true => exact can_neg v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can2 {a} (v : Valid a) : can (can a) = can a := can_flip _ v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma recover (a) : flip (sign a) (can a) = a := flip2 _ _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_zero : can zero = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_one : can one = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipProper (s) {a} (ha : proper a) : proper (flip s a) := by
  cases s
  · exact ha
  · refine ⟨valid_neg ha.1,?_,?_⟩
    · intro h
      exact ha.2.2 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.1))
    · intro h
      exact ha.2.1 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.2))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma canProper {a} (h : proper a) : proper (can a) := flipProper _ h

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sameClass {a b} (h : can a = can b) : a = b ∨ a = neg b := by
  have ha := recover a
  rw [h] at ha
  unfold can at ha
  cases ea : sign a <;> cases eb : sign b <;> simp [ea,eb,flip,neg2] at ha <;> aesop

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_neg_self (d : Bool) {a} (h : Valid a) :
    bin d a (neg a) = (if d then one else zero) := by
  have op {x : Nat} (hx : Valid1 x) :
      x &&& bnot x = 0 ∧ x ||| bnot x = top := by
    constructor <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      simp only [Nat.testBit_and,Nat.testBit_or,testBit_bnot hx,testBit_top,Nat.zero_testBit] <;>
      by_cases hj : j < 128
    all_goals first | (rw [hx j (by omega)] <;> simp [hj]) | (cases x.testBit j <;> simp [hj])
  cases d
  · exact Prod.ext (op h.1).1 (op h.2).1
  · exact Prod.ext (op h.1).2 (op h.2).2

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma distinctClass {d a b} (ha : proper a) (hab : a ≠ b) (hg : proper (bin d a b)) :
    can a ≠ can b := by
  intro h
  rcases sameClass h with e | e
  · exact hab e
  · have eb : b = neg a := by rw [e,neg2]
    rw [eb,bin_neg_self _ ha.1] at hg
    cases d
    · exact hg.2.1 rfl
    · exact hg.2.2 rfl

def blend (d s t : Bool) (a b : Sig) := can (bin d (flip s a) (flip t b))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive BL : Nat → Finset Sig → Prop where
  | stop : BL 0 {can target}
  | step {k U a b d s t} (ha : proper a) (hb : proper b)
      (ac : can a = a) (bc : can b = b) (hab : a ≠ b)
      (fresh : blend d s t a b ∉ insert a (insert b U))
      (tail : BL k (insert (blend d s t a b) U)) : BL (k+1) (insert a (insert b U))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma compress {k t S} (l : Live k t S) :
    ∃ j T, j+t ≤ k ∧ BL j T ∧ T ⊆ S.image can := by
  induction l with
  | stop => exact ⟨0,_,by omega,BL.stop,by simp⟩
  | @unary k t U a ha _ _ ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    refine ⟨j,T,by omega,h,?_⟩
    simpa only [Finset.image_insert,can_neg ha.1] using sub
  | @binary k t U a b d ha hb hab _ tail ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    let g := bin d a b
    let z := can g
    let w := insert (can a) (insert (can b) (U.image can))
    have hsource : (insert a (insert b U)).image can = w := by simp [w]
    rw [hsource]
    have hs : T ⊆ insert z (U.image can) := by simpa [g,z] using sub
    by_cases need : z ∈ T ∧ z ∉ w
    · have hu : T.erase z ⊆ U.image can := by
        intro c hc
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hc))).resolve_left (Finset.ne_of_mem_erase hc)
      have hp : proper g := live_proper tail _ (Finset.mem_insert_self ..)
      have nz := distinctClass ha hab hp
      have id : blend d (sign a) (sign b) (can a) (can b) = z := by
        simp [blend,recover,z,g]
      have out : BL j (insert (blend d (sign a) (sign b) (can a) (can b)) (T.erase z)) := by
        rw [id,Finset.insert_erase need.1]; exact h
      have fresh : blend d (sign a) (sign b) (can a) (can b) ∉ insert (can a) (insert (can b) (T.erase z)) := by
        rw [id]
        intro zz
        apply need.2
        simp only [Finset.mem_insert] at zz ⊢
        simp only [w,Finset.mem_insert]
        exact zz.imp_right (fun e => e.imp_right (fun h => hu h))
      refine ⟨j+1,_,by omega,BL.step (canProper ha) (canProper hb) (can2 ha.1) (can2 hb.1) nz fresh out,?_⟩
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hu)
    · refine ⟨j,T,by omega,h,?_⟩
      intro c hc
      rcases Finset.mem_insert.mp (hs hc) with rfl | hU
      · exact Classical.byContradiction (fun hn => need ⟨hc,hn⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU)


set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.forms {k S} (l : BL k S) : ∀ a ∈ S, proper a ∧ can a = a := by
  induction l with
  | stop => simpa using And.intro (canProper target_proper) (can2 valid_target)
  | step ha hb ca cb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha,ca⟩,⟨hb,cb⟩,fun a h => ih _ (Finset.mem_insert_of_mem h)⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_ne {a} (hv : Valid a) : neg a ≠ a := by
  intro h
  have eq := sign_neg hv
  rw [h] at eq
  cases e : sign a <;> simp [e] at eq

def Present (n : Nat) (S : Finset Sig) := ∃ t, Live (n+t) t S

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma insertFlip {n a U} (s : Bool) (ha : proper a)
    (hf : s = true → neg a ∉ insert a U) (h : Present n (insert (flip s a) U)) :
    Present n (insert a U) := by
  cases s
  · exact h
  · obtain ⟨t,hl⟩ := h
    exact ⟨t+1,by simpa [Nat.add_assoc] using Live.unary ha (hf rfl) hl⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.expand {j S} (l : BL j S) : Present j S := by
  induction l with
  | stop =>
    have eq : can target = neg target := by decide +kernel
    rw [eq]
    have hf : neg (neg target) ∉ insert (neg target) (∅ : Finset Sig) := by
      rw [neg2]; simp [Ne.symm (neg_ne valid_target)]
    have t : Live 0 0 (insert (neg (neg target)) ∅) := by rw [neg2]; exact Live.stop
    exact ⟨1,Live.unary (flipProper true target_proper) hf t⟩
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    let x := flip s a
    let y := flip t b
    let g := bin d x y
    let z := can g
    change z ∉ insert a (insert b U) at fresh
    change Present k (insert z U) at ih
    have cx : can x = a := (can_flip s ha.1).trans ca
    have cy : can y = b := (can_flip t hb.1).trans cb
    have vg : Valid g := valid_bin (vf _ ha.1) (vf _ hb.1)
    have zu : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have canonU (c) (hc : c ∈ U) : can c = c := (tail.forms c (Finset.mem_insert_of_mem hc)).2
    have gz : proper z := (tail.forms _ (Finset.mem_insert_self ..)).1
    have hg : proper g := recover g ▸ flipProper (sign g) gz
    have go := insertFlip (sign g) hg (by
      intro act h
      rcases Finset.mem_insert.mp h with gg | inu
      · exact neg_ne vg gg
      · have zz : z = neg g := by change flip (sign g) g = _; rw [act]; rfl
        exact zu (zz ▸ inu)) ih
    have xy : x ≠ y := fun eq => ne (cx.symm.trans ((congrArg can eq).trans cy))
    have gfresh : g ∉ insert x (insert y U) := by
      intro h
      rcases Finset.mem_insert.mp h with hh | h
      · have za : z = a := (congrArg can hh).trans cx
        exact fresh (Finset.mem_insert.mpr (Or.inl za))
      rcases Finset.mem_insert.mp h with hh | inu
      · have zb : z = b := (congrArg can hh).trans cy
        exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl zb)))
      · apply zu
        change can g ∈ U
        rwa [canonU g inu]
    obtain ⟨negCount,live⟩ := go
    have go2 : Present (k+1) (insert x (insert y U)) := by
      refine ⟨negCount,?_⟩
      convert Live.binary (flipProper s ha) (flipProper t hb) xy gfresh live using 1 <;> omega
    have nap : neg a ∉ U := by
      intro hh
      have eq := canonU (neg a) hh
      rw [can_neg ha.1,ca] at eq
      exact neg_ne ha.1 eq.symm
    have nbp : neg b ∉ U := by
      intro hh
      have eq := canonU (neg b) hh
      rw [can_neg hb.1,cb] at eq
      exact neg_ne hb.1 eq.symm
    have xa := insertFlip s ha (U := insert y U) (fun _ hh => by
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact neg_ne ha.1 eq
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact ne (ca.symm.trans ((can_neg ha.1).symm.trans ((congrArg can eq).trans cy)))
      · exact nap hh) go2
    rw [Finset.insert_comm] at xa
    rw [Finset.insert_comm]
    apply insertFlip t hb _ xa
    intro act hh
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact neg_ne hb.1 eq
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact ne ((cb.symm.trans ((can_neg hb.1).symm.trans ((congrArg can eq).trans ca))).symm)
    · exact nbp hh

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma freeColors {k S} (h : BL k S) : ∃ n, Colored S n ∧ n+S.card ≤ k+2 := by
  obtain ⟨t,hl⟩ := h.expand
  obtain ⟨n,c,b⟩ := live_colored hl
  exact ⟨n,c,by omega⟩

end Free1868

namespace FreeSearch1868
open Basis1868
open Conflict1868 Check1868 Free1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma negFlip (u : Bool) (a : Sig) : neg (flip u a) = flip (!u) a := by
  cases u <;> simp [PEqualNP.Outside.L_meta_10718.Free1868.flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 128 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 128 <;> simp [e]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipBlend {a b} (ha : Valid a) (hb : Valid b) (d s t : Bool) :
    ∃ u v, blend false u v a b = blend d s t a b := by
  cases d
  · exact ⟨s,t,rfl⟩
  · refine ⟨!s,!t,?_⟩
    unfold blend
    rw [← negFlip,← negFlip,← deM (vf s ha) (vf t hb),can_neg (valid_bin (vf s ha) (vf t hb))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_symm (d s t a b) : blend d s t a b = blend d t s b a := by unfold blend; rw [bin_comm]

def keep (a b : Sig) (u v : Bool) (c : Sig) := (c != a || u) && (c != b || v)
def next (v : List Sig) (a b z : Sig) (l r : Bool) := z :: v.filter (keep a b l r)
def oneB (v : List Sig) (go : List Sig → Bool) (a b : Sig) (s t : Bool) :=
  let z := blend false s t a b
  z != zero && !(v.contains z) &&
  ([false,true].any fun l => [false,true].any fun r => go (next v a b z l r))
def pairB (v : List Sig) (go : List Sig → Bool) (a b : Sig) :=
  [false,true].any fun s => [false,true].any fun t => oneB v go a b s t

def baseTest (v : List Sig) := v == [can target]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tailState {a b z : Sig} {U : Finset Sig} {v : List Sig} (nd : v.Nodup)
    (rep : v.toFinset = insert a (insert b U)) (fresh : z ∉ insert a (insert b U)) :
    let w := next v a b z (decide (a ∈ U)) (decide (b ∈ U))
    w.Nodup ∧ w.toFinset = insert z U := by
  classical
  dsimp only
  have ff : (v.filter (keep a b (decide (a ∈ U)) (decide (b ∈ U)))).toFinset = U := by
    ext c
    simp only [List.mem_toFinset,List.mem_filter,keep,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne]
    have mem : c ∈ v ↔ c = a ∨ c = b ∨ c ∈ U := by rw [← List.mem_toFinset,rep]; simp
    rw [mem]
    by_cases ea : c = a <;> by_cases eb : c = b <;> simp_all
  constructor
  · apply List.nodup_cons.mpr
    exact ⟨fun h => fresh (rep ▸ List.mem_toFinset.mpr (List.mem_of_mem_filter h)),nd.filter _⟩
  · simpa only [next,List.toFinset_cons,ff]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma anyBool {f : Bool → Bool} (a) (h : f a = true) : [false,true].any f = true :=
  List.any_eq_true.mpr ⟨a,by cases a <;> simp,h⟩

end FreeSearch1868

namespace Part1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868

end Part1868

namespace Full1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868

end Full1868

namespace Cuts1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868 Full1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma oneStep {k S} (l : BL k S) (m : Nat) (hm : k ≤ m+1) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset = S) (go : List Sig → Bool)
    (hyp : ∀ w, w.Nodup → ∀ j ≤ m, BL j w.toFinset → go w = true) :
    (baseTest v || scanPairs (pairB v go) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr; right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (id : blend false u w x y = z)
        (eqS : v.toFinset = insert x (insert y U)) : pairB v go x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      exact hyp _ nw j (by omega) (pw ▸ tail)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w id rep
    · exact yes b a w u ((blend_symm false w u b a).trans id) (by rwa [Finset.insert_comm b a])



def excluded (k : Nat) (v : List Sig) := ∀ n ≤ k, ¬ BL n v.toFinset
end Cuts1868

namespace FastCuts1868
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Part1868 Full1868 Cuts1868

end FastCuts1868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868
namespace Board1868
open Basis1868
def mult : List (Sig × Nat) → Sig
  | [] => zero
  | o::l => let (atLeastOne,atLeastTwo) := mult l
            (atLeastOne ||| o.2,atLeastTwo ||| (atLeastOne &&& o.2))
end Board1868
namespace LinearWide1868
open Basis1868 Board1868
end LinearWide1868
namespace Linear1868
def Linear (f : Nat → Nat) := f 0 = 0 ∧ ∀ x y, f (x ||| y) = f x ||| f y
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linId : Linear id := ⟨rfl,fun _ _ => rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linAnd (mask : Nat) : Linear (fun x => x &&& mask) :=
  ⟨by simp,fun _ _ => Nat.and_or_distrib_right ..⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linLeft (n : Nat) : Linear (fun x => x <<< n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_shiftLeft,Nat.testBit_or]
    by_cases e : n ≤ j <;> simp [e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linRight (n : Nat) : Linear (fun x => x >>> n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp [Nat.testBit_shiftRight,Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linOr {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ||| g x) :=
  ⟨by simp [hf.1,hg.1],fun x y => by dsimp only; rw [hf.2,hg.2]; ac_rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linComp {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f (g x)) :=
  ⟨by dsimp only; rw [hg.1,hf.1],fun _ _ => by dsimp only; rw [hg.2,hf.2]⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma trunc_succ (x n : Nat) : x % 2^(n+1) = (x % 2^n) ||| (if x.testBit n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_or]
  cases e : x.testBit n <;> by_cases h : j=n <;> by_cases lt : j<n <;>
    simp_all [Nat.testBit_two_pow, show (j < n+1) ↔ j<n ∨ j=n by omega] <;> omega
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma imagesTrunc {f : Nat→Nat} (hl : Linear f) (x j) (n : Nat) :
    (f (x % 2^n)).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  induction n with
  | zero => simp [Nat.mod_one,hl.1]
  | succ n ih =>
    rw [trunc_succ,hl.2,Nat.testBit_or,Bool.or_eq_true,ih]
    by_cases bit : x.testBit n = true
    · simp only [bit,↓reduceIte]
      constructor
      · rintro (⟨i,hi,hb,hv⟩|h)
        · exact ⟨i,by omega,hb,hv⟩
        · exact ⟨n,by omega,bit,h⟩
      · rintro ⟨i,hi,hb,hv⟩
        by_cases e : i=n
        · exact Or.inr (e ▸ hv)
        · exact Or.inl ⟨i,by omega,hb,hv⟩
    · simp only [bit,↓reduceIte,hl.1,Nat.zero_testBit,Bool.false_eq_true,or_false]
      constructor
      · rintro ⟨i,hi,hb,hv⟩; exact ⟨i,by omega,hb,hv⟩
      · rintro ⟨i,hi,hb,hv⟩
        have ne : i ≠ n := fun e => bit (e ▸ hb)
        exact ⟨i,by omega,hb,hv⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma images {f : Nat→Nat} (hl : Linear f) {x n} (lim : x < 2^n) (j) :
    (f x).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  simpa [Nat.mod_eq_of_lt lim] using imagesTrunc hl x j n
end Linear1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma validBound {x} (h : Valid1 x) : x < 2^128 := by
  have eq : x % 2^128 = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < 128
    · simp [hj]
    · simp [hj,h j (by omega)]
  rw [← eq]
  exact Nat.mod_lt _ (by decide)
def Sub (x y : Nat) := ∀ i, x.testBit i = true → y.testBit i = true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linMono {f} (h : Linear f) {x y} (s : Sub x y) : Sub (f x) (f y) := by
  have e : x ||| y = y := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
    cases hx : x.testBit i <;> simp [hx,s i]
  intro i hi
  have e' := congrArg (fun w : Nat => w.testBit i) (h.2 x y)
  simp [e,Nat.testBit_or,hi] at e'
  exact e'
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
abbrev Ix := Fin 26496
abbrev I := Fin 128
def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then PEqualNP.Outside.L_meta_10718.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
open PEqualNP.Outside.L_meta_10718.Board1868 (mult)
abbrev Sign := Sig × Nat
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma multiOne {v : List Sign} {a} (ha : a ∈ v) (i) (hit : a.2.testBit i = true) :
    (mult v).1.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).1 ||| z.2).testBit i = true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl|hh
    · exact Or.inr hit
    · exact Or.inl (ih hh)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma multiTwo {v : List Sign} {a b} (ha : a∈v) (hb : b∈v) (ne : a ≠ b) (i)
    (x : a.2.testBit i = true) (y : b.2.testBit i = true) : (mult v).2.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).2 ||| ((mult l).1 &&& z.2)).testBit i = true
    rw [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true]
    rcases List.mem_cons.mp ha with ea|hal
    · subst a
      rcases List.mem_cons.mp hb with eb|hbl
      · exact (ne eb.symm).elim
      · exact Or.inr ⟨multiOne hbl i y,x⟩
    · rcases List.mem_cons.mp hb with eb|hbl
      · subst b
        exact Or.inr ⟨multiOne hal i x,y⟩
      · exact Or.inl (ih hal hbl)

def U (d : Bool) (p n : I) (v : List Sig) (a : Sig) := ∀ c ∈ v, DS d p n c → c=a
def M (d : Bool) (p n : I) (v : List Sig) (a : Sig) :=
  DS d p n a ∧ (∃ j,U d p j v a) ∧ ∃ j,U d j n v a
end WProof1868
namespace Guard3400
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open WProof1868 LinearWide1868
open PEqualNP.Outside.L_meta_10718.Board1868 (mult)
open PEqualNP.Outside.L_meta_10718.ColorSearch1868 (paint paint_ok)

end Guard3400
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868
namespace Check2516
def costly (g : Gate) : Bool := match g.op with | .not => false | _ => true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gateTag {w : List Sig} (hw : ∀ a∈w, Valid a) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ (∃ a∈w, proper a ∧ gv w g=neg a) ∨
      ((if costly g then 1 else 0)=1 ∧ ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ gv w g=bin d a b) := by
  by_cases h : costly g=true
  · rcases gate_rep hw g legal with a|a|a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨by simp [h],a⟩)
  · obtain ⟨o,l⟩ := g
    cases o <;> try simp [costly] at h
    have nt (a : Sig) (v : Valid a) (r : represented w a) :
        represented w (neg a) ∨ ∃ a'∈w, proper a' ∧ neg a=neg a' := by
      rcases operand_cases v r with rfl|rfl|⟨mem,hp⟩
      · exact Or.inl (Or.inr (fun hp => hp.2.2 neg_laws.1))
      · exact Or.inl (Or.inr (fun hp => hp.2.1 neg_laws.2))
      · exact Or.inr ⟨a,mem,hp,rfl⟩
    cases l with
    | nil => exact (nt zero valid_zero (Or.inr (fun h => h.2.1 rfl))).imp_right Or.inl
    | cons i l => exact (nt (w.getD i zero) (valid_getD hw i) (get_rep w i)).imp_right Or.inl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pullTag (c : Nat) {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ (∃ a ∈ w, proper a ∧ z=neg a) ∨ (c=1 ∧ ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k+t'+c ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨hc,d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tagExtract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.countP costly + t ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pullTag (if costly g then 1 else 0) ht (gateTag hw g (legal g (by simp))) hs
    exact ⟨l,u,T,by cases he : costly g <;> simp [he] at hl ⊢ <;> omega,hu,hT⟩
end Check2516
namespace Check2516
open Basis1868 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
end Check2516
namespace Basis1868
def reindexLoop (f : Fin 128 → Fin 128) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 128 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 128 → Fin 128) (x : Nat) : Nat := reindexLoop f x 128
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindexLoop_testBit (f : Fin 128 → Fin 128) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 128 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 128
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 128 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 128 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 128
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_testBit (f : Fin 128 → Fin 128) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 128 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 128 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_valid1 (f : Fin 128 → Fin 128) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 128 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_and (f : Fin 128 → Fin 128) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 128 <;> simp [hj, Nat.testBit_and]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_or (f : Fin 128 → Fin 128) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 128 <;> simp [hj, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_bnot (f : Fin 128 → Fin 128) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 128
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_zero (f : Fin 128 → Fin 128) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_top (f : Fin 128 → Fin 128) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 128
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 128 → Fin 128) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)

end Basis1868
namespace Sym1868
open Basis1868
def Good (H J : SigHom) (a : Sig) := Valid a ∧ J.fn (H.fn a) = a
variable {H J : SigHom}
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodNeg {a} (h : Good H J a) : Good H J (neg a) :=
  ⟨valid_neg h.1,by rw [H.hneg h.1,J.hneg (H.valid a),h.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBin {a b} (ha : Good H J a) (hb : Good H J b) {d} : Good H J (bin d a b) :=
  ⟨valid_bin ha.1 hb.1,by rw [H.hbin,J.hbin,ha.2,hb.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma inj {a b} (ha : Good H J a) (hb : Good H J b) (e : H.fn a = H.fn b) : a=b := by
  rw [← ha.2,← hb.2,e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma properH {a} (ga : Good H J a) (ha : proper a) : proper (H.fn a) :=
  ⟨H.valid a,fun e => ha.2.1 (ga.2.symm.trans ((congrArg J.fn e).trans J.hzero)),
    fun e => ha.2.2 (ga.2.symm.trans ((congrArg J.fn e).trans J.hone))⟩
end Sym1868
namespace Moves3400
open Basis1868
open Free1868 Sym1868 Cuts1868
def SignFixed (H : SigHom) := ∀ a, sign (H.fn a)=sign a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip_map (H : SigHom) (s : Bool) {a : Sig} (ha : Valid a) :
    H.fn (flip s a)=flip s (H.fn a) := by cases s <;> first | rfl | exact H.hneg ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_map {H : SigHom} (fix : SignFixed H) {a : Sig} (ha : Valid a) :
    H.fn (can a)=can (H.fn a) := by unfold can; rw [fix a,flip_map H _ ha]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_map {H : SigHom} (fix : SignFixed H) {a b : Sig} (ha : Valid a) (hb : Valid b) (d s t) :
    H.fn (blend d s t a b)=blend d s t (H.fn a) (H.fn b) := by
  unfold blend
  rw [can_map fix (valid_bin (vf s ha) (vf t hb)),H.hbin,flip_map H _ ha,flip_map H _ hb]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodFlip {H J : SigHom} {a} (h : Good H J a) (s : Bool) : Good H J (flip s a) := by
  cases s <;> first | exact h | exact goodNeg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBlend {H J : SigHom} {a b} (ha : Good H J a) (hb : Good H J b) (d s t) :
    Good H J (blend d s t a b) := goodFlip (goodBin (goodFlip ha s) (goodFlip hb t)) _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mapBL {H J : SigHom} (fix : SignFixed H) {k S} (l : BL k S) (hs : ∀ a∈S,Good H J a) :
    BL k (S.image H.fn) := by
  induction l with
  | stop => simpa only [Finset.image_singleton,can_map fix target_proper.1,H.htarget] using (BL.stop : BL 0 {can target})
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    have ga := hs a (Finset.mem_insert_self ..)
    have gb := hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have gu (x) (h : x∈U) : Good H J x := hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have gz := goodBlend ga gb d s t
    have ez := blend_map fix ha.1 hb.1 d s t
    have ht := ih (by simpa only [Finset.forall_mem_insert] using And.intro gz gu)
    rw [Finset.image_insert,ez] at ht
    rw [Finset.image_insert,Finset.image_insert]
    apply BL.step (properH ga ha) (properH gb hb) _ _ (fun e => ne (inj ga gb e)) _ ht
    · rw [← can_map fix ha.1,ca]
    · rw [← can_map fix hb.1,cb]
    · rw [← ez,← Finset.image_insert,← Finset.image_insert]
      intro h
      obtain ⟨x,hx,xe⟩ := Finset.mem_image.mp h
      exact fresh (inj (hs x hx) gz xe ▸ hx)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fixed (p n : Fin 128 → Fin 128) (z : p 0=0) : SignFixed (pairHom p n) := by
  intro a
  change (reindex p a.1).testBit 0=a.1.testBit 0
  rw [reindex_testBit]
  simp [z]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma move {v w : List Sig} {k : Nat} (H J : SigHom) (fix : SignFixed H)
    (equal : (v.map H.fn).toFinset=w.toFinset)
    (inverse : v.all (fun a => decide (J.fn (H.fn a)=a))=true)
    (old : excluded k w) : excluded k v := by
  intro m hm l
  have h := mapBL (J:=J) fix l (fun a ha => ⟨(l.forms a ha).1.1,
    of_decide_eq_true (List.all_eq_true.mp inverse a (List.mem_toFinset.mp ha))⟩)
  have eq : v.toFinset.image H.fn=(v.map H.fn).toFinset := by
    ext x; simp
  rw [eq,equal] at h
  exact old _ hm h
end Moves3400
namespace Mono1868
open Basis1868

abbrev I := Fin 128
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def pos (x y : Bool) : Prop := x = true ∧ y = false
def D (p n : I) (a : Sig) : Prop := pos (P a p) (N a n)
def op (d x y : Bool) : Bool := if d then x || y else x && y

lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
lemma bor : ∀ (d ap an bp bn : Bool), pos (op d ap bp) (op d an bn) → pos ap an ∨ pos bp bn := by
  unfold pos; decide +kernel
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  unfold D P N at hd
  rw [bop,bop] at hd
  exact bor _ _ _ _ _ hd
lemma pair_sep {k t S} (hl : Live k t S) (ht : t = 0) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,pos,P,N,bit,target,testBit_top,p.isLt]
  | unary => omega
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (ht : t=0) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h ht p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

lemma mix : ∀ (d ap an bp bn al ar bm bq : Bool), pos ap an →
    ¬ pos bp bm → ¬ pos bq bn →
    pos (op d ap bp) (op d al bm) → pos (op d ar bq) (op d an bn) →
    ¬ pos bp bn ∧ pos (op d ap bp) (op d an bn) := by unfold pos; decide +kernel

lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U)) (ht : t = 0)
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : ¬ pos (P b p) (N b m) := fun h => hab (hm _ hb h).symm
  have bq : ¬ pos (P b q) (N b n) := fun h => hab (hq _ hb h).symm
  have zm := unique_diff tail ht (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail ht (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  unfold D P N at zm zq
  rw [bop,bop] at zm zq
  have hh := mix _ _ _ _ _ _ _ _ _ hd bm bq zm zq
  refine ⟨hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2


def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (ht : t=0) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ht ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail ht mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

theorem live_colored {k t S} (l : Live k t S) (ht : t=0) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary => omega
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih ht
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail ht hk
    exact ⟨u,hu,by omega⟩

end Mono1868
end PEqualNP.Outside.L_meta_10718
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_10718
def edge (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)
end PEqualNP.Outside.L_meta_10718
namespace PEqualNP.Outside.L_meta_10718
section
open Basis1868 Free1868
namespace Projection8403
def unaryRep (w : List Sig) (z : Sig) := ∃ a∈w,proper a ∧ z=neg a
def binRep (w : List Sig) (z : Sig) := ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b
lemma pullBudget {w : List Sig} {z : Sig} {k t S} {cost : Nat} (h : Live k t S)
    (hz : represented w z ∨ unaryRep w z ∨ (0 < cost ∧ binRep w z)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k + t' + cost ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨positive,d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha

def Can (cost : Nat) (base : Finset Sig) := ∃ k t T,k≤cost+t ∧ Live k t T ∧ T⊆base
lemma mono {m n a b} (h : Can m a) (budget : m≤n) (sub : a⊆b) : Can n b := by
  obtain ⟨u,t,T,cap,run,incl⟩:=h;exact ⟨u,t,T,by omega,run,incl.trans sub⟩
lemma rewind {q basis z cost} (step : represented basis.toList z ∨ unaryRep basis.toList z ∨
      0<cost ∧ binRep basis.toList z) (tail : Can q (insert z basis)) : Can (q+cost) basis := by
  obtain ⟨k,t,T,le,h,sub⟩:=tail
  have avail : ∀a∈T,a∈basis.toList++[z] := by
    intro a ha;rcases Finset.mem_insert.mp (sub ha) with rfl|hm
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr hm)
  obtain ⟨k',t',T',cap,live,old⟩:=pullBudget h step avail
  exact ⟨k',t',T',by omega,live,fun a ha=>Finset.mem_toList.mp (old a ha)⟩
lemma negStep {basis : Finset Sig} {a : Sig} (va : Valid a) (ha : a∈basis) :
    represented basis.toList (neg a) ∨ unaryRep basis.toList (neg a) ∨ 0<0 ∧ binRep basis.toList (neg a) := by
  by_cases p : proper a
  · exact Or.inr (Or.inl ⟨a,Finset.mem_toList.mpr ha,p,rfl⟩)
  · rcases operand_cases va (Or.inr p : represented [] a) with rfl|rfl|⟨bad,_⟩
    · rw [neg_laws.1];exact Or.inl (Or.inr (fun p=>p.2.2 rfl))
    · rw [neg_laws.2];exact Or.inl (Or.inr (fun p=>p.2.1 rfl))
    · cases bad
lemma binaryStep {basis : Finset Sig} {a b : Sig} (d) (va : Valid a) (vb : Valid b) (ha : a∈basis) (hb : b∈basis) :
    represented basis.toList (bin d a b) ∨ unaryRep basis.toList (bin d a b) ∨ 0<1 ∧ binRep basis.toList (bin d a b) := by
  rcases bin_rep d va vb (Or.inl (Finset.mem_toList.mpr ha)) (Or.inl (Finset.mem_toList.mpr hb)) with r|u|v
  · exact Or.inl r
  · exact Or.inr (Or.inl u)
  · exact Or.inr (Or.inr ⟨by decide,v⟩)
def constant (a : Sig) := a=zero ∨ a=one
instance (a : Sig) : Decidable (constant a) := by unfold constant;infer_instance
def mass (H : SigHom) (s : Finset Sig) := (s.filter (fun a=>constant (H.fn a))).card
lemma constant_neg {a : Sig} (va : Valid a) : constant (neg a) ↔ constant a := by
  constructor
  · rintro (e|e)
    · right;simpa only [neg2,neg_laws.1] using (show neg (neg a)=neg zero from congrArg neg e)
    · left;simpa only [neg2,neg_laws.2] using congrArg neg e
  · rintro (rfl|rfl)
    · right;exact neg_laws.1
    · left;exact neg_laws.2
lemma constResult {a b : Sig} (va : Valid a) (vb : Valid b) (d : Bool) (c : constant a ∨ constant b) :
    constant (bin d a b) ∨ bin d a b=a ∨ bin d a b=b := by
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws va
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws vb
  rcases c with (rfl|rfl)|(rfl|rfl) <;> cases d <;> simp_all [constant,bin_comm]
lemma bothResult {a b : Sig} (va : Valid a) (vb : Valid b) (d) (ca : constant a) (cb : constant b) :
    constant (bin d a b) := by
  rcases constResult va vb d (Or.inl ca) with h|h|h
  · exact h
  · simpa only [h] using ca
  · simpa only [h] using cb
lemma constFree {basis : Finset Sig} {a b : Sig} (va : Valid a) (vb : Valid b) (ha : a∈basis) (hb : b∈basis)
    (d) (c : constant a ∨ constant b) : represented basis.toList (bin d a b) := by
  rcases constResult va vb d c with (h|h)|h|h
  · exact Or.inr (fun p=>p.2.1 h)
  · exact Or.inr (fun p=>p.2.2 h)
  · apply Or.inl;rw [h];exact Finset.mem_toList.mpr ha
  · apply Or.inl;rw [h];exact Finset.mem_toList.mpr hb
end Projection8403
end
section
open Basis1868 Free1868
namespace Projection8403
lemma massInsert (H : SigHom) (a : Sig) (U : Finset Sig) :
    mass H (insert a U) = mass H U + (if a∉U ∧ constant (H.fn a) then 1 else 0) := by
  classical
  by_cases mem : a∈U
  · simp [mem,Finset.insert_eq_of_mem mem]
  · by_cases c : constant (H.fn a)
    · simp [mass,Finset.filter_insert,mem,c,Finset.card_insert_of_notMem]
    · simp [mass,Finset.filter_insert,mem,c]
lemma pushNeg {H : SigHom} {q : Nat} {U : Finset Sig} {a : Sig} (va : Valid a)
    (tail : Can q ((insert (neg a) U).image H.fn)) : Can q ((insert a U).image H.fn) := by
  let pool:=(insert a U).image H.fn
  have ha : H.fn a∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have sub : (insert (neg a) U).image H.fn⊆insert (neg (H.fn a)) pool := by
    rw [Finset.image_insert,H.hneg va]
    exact Finset.insert_subset_insert _ (Finset.image_mono _ (Finset.subset_insert ..))
  simpa only [Nat.add_zero,pool] using rewind (negStep (H.valid a) ha) (mono tail (Nat.le_refl _) sub)
lemma pushBin {H : SigHom} {q : Nat} {U : Finset Sig} {a b : Sig} (d : Bool) (tail : Can q ((insert (bin d a b) U).image H.fn)) :
    Can (q+(if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1)) ((insert a (insert b U)).image H.fn) := by
  let pool:=(insert a (insert b U)).image H.fn
  have ha : H.fn a∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  have hb : H.fn b∈pool:=Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have sub : (insert (bin d a b) U).image H.fn ⊆ insert (bin d (H.fn a) (H.fn b)) pool := by
    rw [Finset.image_insert,H.hbin]
    apply Finset.insert_subset_insert
    exact Finset.image_mono _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..))
  by_cases c : constant (H.fn a) ∨ constant (H.fn b)
  · rw [ite_eq_left c]
    apply rewind (Or.inl (constFree (H.valid a) (H.valid b) ha hb d c))
    exact mono tail (Nat.le_refl _) sub
  · rw [ite_eq_right c]
    exact rewind (binaryStep d (H.valid a) (H.valid b) ha hb) (mono tail (Nat.le_refl _) sub)
lemma massNeg {H : SigHom} {U : Finset Sig} {a : Sig} (va : Valid a) (fresh : neg a∉insert a U) :
    mass H (insert a U)≤mass H (insert (neg a) U) := by
  have hz : neg a∉U:=fun zn=>fresh (Finset.mem_insert_of_mem zn)
  rw [massInsert,massInsert,H.hneg va]
  simp only [hz,not_false_eq_true,true_and,constant_neg (H.valid a)]
  by_cases c : constant (H.fn a) <;> by_cases t : a∈U <;> simp [c,t]
lemma massBin {H : SigHom} {U : Finset Sig} {a b : Sig} (d : Bool) (ab : a≠b) (fresh : bin d a b∉insert a (insert b U)) :
    mass H (insert a (insert b U)) + (if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1) ≤
      mass H (insert (bin d a b) U)+1 := by
  have hz : bin d a b∉U:=fun z=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem z))
  rw [massInsert,massInsert,massInsert,H.hbin]
  by_cases ca : constant (H.fn a) <;> by_cases cb : constant (H.fn b)
  all_goals by_cases aa : a∈U <;> by_cases bb : b∈U
  all_goals simp only [Finset.mem_insert,ab,false_or,ca,cb,aa,bb,hz,not_true_eq_false,not_false_eq_true,
    and_false,false_and,true_and,and_true,ite_false,ite_true,or_false,false_or,true_or,or_true,Nat.add_zero]
  all_goals try omega
  all_goals try (have z:=bothResult (H.valid a) (H.valid b) d ca cb; rw [ite_eq_left z]; omega)
  all_goals try (split <;> omega)
  all_goals
    have z := bothResult (H.valid a) (H.valid b) d ca cb
    simp only [z,ite_true]
    omega
theorem projected {k t S} (h : Live k t S) (H : SigHom) :
    ∃ q,q+mass H S+t≤k ∧ Can q (S.image H.fn) := by
  induction h with
  | stop =>
    have nc : ¬constant target:=by rintro (e|e);exact target_proper.2.1 e;exact target_proper.2.2 e
    refine ⟨0,by simp [mass,H.htarget,nc],0,0,{target},by omega,Live.stop,?_⟩
    simp [H.htarget]
  | @unary k t U a ha hf tail ih =>
    obtain ⟨q,cap,prog⟩:=ih
    have le:=massNeg (H:=H) ha.1 hf
    exact ⟨q,by omega,pushNeg ha.1 prog⟩
  | @binary k t U a b d ha hb ab hf tail ih =>
    obtain ⟨q,cap,prog⟩:=ih
    have le:=massBin (H:=H) d ab hf
    exact ⟨q+(if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1),by omega,pushBin d prog⟩
theorem projectedBL {n S} (run : BL n S) (H : SigHom) :
    ∃k T,k+mass H S≤n ∧ BL k T ∧ T⊆(S.image H.fn).image can := by
  obtain ⟨t,live⟩:=run.expand
  obtain ⟨q,lim,m,u,T,cap,h,sub⟩:=projected live H
  obtain ⟨j,V,size,ok,ss⟩:=compress h
  exact ⟨j,V,by omega,ok,ss.trans (Finset.image_mono _ sub)⟩
end Projection8403
end
section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Check2516 Free1868 FreeSearch1868 Cuts1868
open Projection8403 PEqualNP.Outside.L_meta_10718
namespace Exact8403
def raw8 : List Sig := [(0x6adbaaaaaaab55555556aaad55b56adb,0x8a008a008a008a008a008a008a008a), (0xb36ecccccccd9999999b333666d9b36e,0x2c002c002c002c002c002c002c002c), (0x3c73f0f0f0f1e1e1e1e3c3c7871e3c73,0x11301130113011301130113011301130), (0xc07cff00ff01fe01fe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0), (0xff80ffff0001fffe0003fff8001fff80,0x26002600260026002600260026002600), (0xfffffffe00000003ffffffe00000,0xb800b800b800b800b800b800b800b800), (0xfffffffffffffffc000000000000,0xc000c000c000c000c000c000c000c000)]
def pos8 : Array Nat := #[5, 7, 10, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
def neg8 : Array Nat := #[0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 24, 32, 36, 48, 64, 96]
def sample8 (s : Bool) (i : Fin 128) : Fin 7 → Bool :=
  let xs:=if s then pos8 else neg8
  fun j=>(xs.getD (i.val % xs.size) 0).testBit j.val
lemma vals : ∀a∈raw8,Valid a := by
  have h : raw8.all (fun x=>decide (x.1≤top ∧ x.2≤top))=true := by decide +kernel
  intro a ha
  have k:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top k.1,valid1_of_le_top k.2⟩
set_option maxHeartbeats 0 in
lemma good8 : ∀(s : Bool) (i : Fin 128), edge (sample8 s i)=s ∧ List.ofFn (sample8 s i)=raw8.map (bit s i) := by decide +kernel
lemma output8 {C : Circuit} (fan : FanInTwo C) (spec : ∀x, C.eval (List.ofFn x)=edge x) :
    target∈execute C.gates raw8 := by
  let w:=execute C.gates raw8
  have hwv:=execute_valid C.gates raw8 vals
  have hp (s : Bool) (i : Fin 128) : bit s i (w.getD C.output zero)=s := by
    rw [←b_read]
    change ((execute C.gates raw8).map _).getD C.output false=s
    rw [execute_bits _ _ _ _ vals (fun g hg=>(fan g hg).1)]
    have h:=spec (sample8 s i)
    rw [(good8 s i).1,(good8 s i).2] at h
    exact h
  have hvout:=valid_getD hwv C.output
  have et : w.getD C.output zero=target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq;intro j
      rw [target,testBit_top]
      by_cases hi : j<128
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)];simp [hi]
    · apply Nat.eq_of_testBit_eq;intro j
      by_cases hi : j<128
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)];exact (Nat.zero_testBit j).symm
  have rep:=get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun h=>h target_proper)
def necessary (v : List Sig) := ∀a∈v,∃p n : Fin 128,∀b∈v,bit true p b≠bit false n b → b=a
lemma allNeeded {k t S} {v : List Sig} (h : Live k t S) (sub : S⊆v.toFinset) (need : necessary v) : S=v.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨p,n,uniq⟩:=need a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩:=PEqualNP.Outside.L_meta_10718.Conflict1868.pair_sep h p n
  exact uniq b (List.mem_toFinset.mp (sub hb)) sep ▸ hb
def necessaryAt (v : List Sig) (pn : List (Nat×Nat)) :=
  (v.zip pn).all fun (a,p,n) => v.all fun b=>bit true (Fin.ofNat 128 p) b == bit false (Fin.ofNat 128 n) b || b==a
lemma needFrom {v : List Sig} {pn : List (Nat×Nat)} (len : v.length≤pn.length) (ok : necessaryAt v pn=true) : necessary v := by
  intro a ha
  obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp ha
  have hp : i<pn.length:=by omega
  have hz : (a,pn[i])∈v.zip pn := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp;omega,by simp [eq]⟩
  have h:=List.all_eq_true.mp ok _ hz
  refine ⟨Fin.ofNat 128 pn[i].1,Fin.ofNat 128 pn[i].2,?_⟩
  intro b hb no
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp h _ hb) with e|e
  · exact False.elim (no (beq_iff_eq.mp e))
  · exact beq_iff_eq.mp e
end Exact8403
end
section
open Basis1868
open Conflict1868 Free1868 FreeSearch1868 Cuts1868
open Linear1868
namespace QuickQ

abbrev Move := Bool × Nat × Nat
def update (op : Move) (x : Nat) :=
  (if op.1 then x ||| (x <<< op.2.1) else x ||| (x >>> op.2.1)) &&& op.2.2
def sweep : List Move → Nat → Nat
  | [],x => x
  | h::t,x => sweep t (update h x)
theorem linUpdate (op : Move) : Linear (update op) := by
  rcases op with ⟨b,m,n⟩
  cases b
  · exact linComp (f:=fun x=>x &&& n) (g:=fun x=>x ||| (x >>> m)) (linAnd n) (linOr linId (linRight m))
  · exact linComp (f:=fun x=>x &&& n) (g:=fun x=>x ||| (x <<< m)) (linAnd n) (linOr linId (linLeft m))
theorem linSweep (xs : List Move) : Linear (sweep xs) := by
  induction xs with
  | nil => exact linId
  | cons h t ih => exact linComp (f:=sweep t) (g:=update h) ih (linUpdate h)

structure Chart where
  h : Nat
  w : Nat
  spreadP : List Move
  spreadN : List Move
  fillP : List Move
  fillN : List Move

def area (c : Chart) := c.h*c.w
def roof (c : Chart) := 2^(area c)-1
def lanes (c : Chart) := (roof c)/(2^c.w-1)
def row (c : Chart) (i : Nat) := (2^c.w-1) <<< (c.w*i)
def col (c : Chart) (i : Nat) := lanes c <<< i
def positive (c : Chart) (i : Fin (area c)) : Fin 128 := Fin.ofNat 128 (i.val/c.w)
def negative (c : Chart) (i : Fin (area c)) : Fin 128 := Fin.ofNat 128 (i.val % c.w)
def good (c : Chart) :=
  (∀i : Fin 128, sweep c.spreadP (2^i.val) = if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 128, sweep c.spreadN (2^i.val) = if i.val<c.w then col c i.val else 0) ∧
  (∀i : Fin (area c), (row c (positive c i).val).testBit i.val=true ∧
      (col c (negative c i).val).testBit i.val=true) ∧
  (∀(i : Fin (area c)) (p : Fin c.h), (row c p.val).testBit i.val=true → (positive c i).val=p.val) ∧
  (∀(i : Fin (area c)) (n : Fin c.w), (col c n.val).testBit i.val=true → (negative c i).val=n.val) ∧
  (∀i : Fin (area c), (positive c i).val<c.h ∧ (negative c i).val<c.w) ∧
  (∀r : Fin c.h, sweep c.fillP (roof c ^^^ row c r.val) &&& row c r.val = 0) ∧
  (∀n : Fin c.w, sweep c.fillN (roof c ^^^ col c n.val) &&& col c n.val = 0)
theorem roofBit (c : Chart) (i : Nat) : (roof c).testBit i=decide (i<area c) := by
  simp [roof,Nat.testBit_two_pow_sub_one]
theorem locate {f : Nat→Nat} {mask top x i : Nat} (lin : Linear f) (hm : mask.testBit i=true)
    (hc : f (top ^^^ mask) &&& mask = 0) (bx : PEqualNP.Outside.L_meta_10718.WProof1868.Sub x top)
    (hit : (f x).testBit i=true) : ∃j,x.testBit j=true ∧ mask.testBit j=true := by
  by_contra! hn
  have sub : PEqualNP.Outside.L_meta_10718.WProof1868.Sub x (top ^^^ mask) := by
    intro j hj; simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hh:=PEqualNP.Outside.L_meta_10718.WProof1868.linMono lin sub i hit
  have bad:=congrArg (fun z : Nat=>z.testBit i) hc
  simp [Nat.testBit_and,hh,hm] at bad

theorem pbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadP a).testBit i.val = a.testBit (positive c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10718.WProof1868.validBound va)]
  constructor
  · rintro ⟨j,hj,bit,x⟩
    rw [h.1 ⟨j,hj⟩] at x
    by_cases e : j<c.h
    · simp only [e,↓reduceIte] at x
      rw [h.2.2.2.1 i ⟨j,e⟩ x];exact bit
    · simp [e] at x
  · intro x
    refine ⟨_,(positive c i).isLt,x,?_⟩
    rw [h.1 (positive c i), ite_eq_left (h.2.2.2.2.2.1 i).1]
    exact (h.2.2.1 i).1
theorem nbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadN a).testBit i.val = a.testBit (negative c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10718.WProof1868.validBound va)]
  constructor
  · rintro ⟨j,hj,bit,x⟩
    rw [h.2.1 ⟨j,hj⟩] at x
    by_cases e : j<c.w
    · simp only [e,↓reduceIte] at x
      rw [h.2.2.2.2.1 i ⟨j,e⟩ x];exact bit
    · simp [e] at x
  · intro x
    refine ⟨_,(negative c i).isLt,x,?_⟩
    rw [h.2.1 (negative c i),ite_eq_left (h.2.2.2.2.2.1 i).2]
    exact (h.2.2.1 i).2
end QuickQ
end
section
open Basis1868
namespace QuickQ
def compactGood (c : Chart) :=
  (∀i : Fin 128,sweep c.spreadP (2^i.val)=if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 128,sweep c.spreadN (2^i.val)=if i.val<c.w then col c i.val else 0) ∧
  (∀i : Fin (area c),(row c (positive c i).val).testBit i.val=true ∧ (col c (negative c i).val).testBit i.val=true ∧
      (positive c i).val<c.h ∧ (negative c i).val<c.w) ∧
  (∀p q : Fin c.h,p≠q → row c p.val &&& row c q.val=0) ∧
  (∀p q : Fin c.w,p≠q → col c p.val &&& col c q.val=0) ∧
  (∀r : Fin c.h,sweep c.fillP (roof c ^^^ row c r.val) &&& row c r.val=0) ∧
  (∀n : Fin c.w,sweep c.fillN (roof c ^^^ col c n.val) &&& col c n.val=0)
theorem goodOfCompact {c : Chart} (h : compactGood c) : good c := by
  obtain ⟨sp,sn,sel,rows,cols,fp,fn⟩:=h
  refine ⟨sp,sn,fun i=>⟨(sel i).1,(sel i).2.1⟩,?_,?_,fun i=>(sel i).2.2,fp,fn⟩
  · intro i p hp
    let q : Fin c.h:=⟨(positive c i).val,(sel i).2.2.1⟩
    by_contra ne
    have bad:=congrArg (fun z : Nat=>z.testBit i.val) (rows q p (fun eq=>ne (congrArg Fin.val eq)))
    change (row c (positive c i).val &&& row c p.val).testBit i.val=(0 : Nat).testBit i.val at bad
    simp only [Nat.testBit_and,(sel i).1,hp,Nat.zero_testBit] at bad
    contradiction
  · intro i n hn
    let q : Fin c.w:=⟨(negative c i).val,(sel i).2.2.2⟩
    by_contra ne
    have bad:=congrArg (fun z : Nat=>z.testBit i.val) (cols q n (fun eq=>ne (congrArg Fin.val eq)))
    change (col c (negative c i).val &&& col c n.val).testBit i.val=(0 : Nat).testBit i.val at bad
    simp only [Nat.testBit_and,(sel i).2.1,hn,Nat.zero_testBit] at bad
    contradiction
end QuickQ
end
section
open Basis1868
open Free1868 FreeSearch1868 Cuts1868 Conflict1868
open PEqualNP.Outside.L_meta_10718.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_10718.Board1868 (mult)
open PEqualNP.Outside.L_meta_10718.ColorSearch1868 (paint paint_ok)
namespace QuickQ
def diff (c : Chart) (d : Bool) (a : Sig) : Sig × Nat :=
  let p:=sweep c.spreadP a.1
  let n:=sweep c.spreadN a.2
  (a,if d then p ^^^ n else p &&& (roof c ^^^ n))
def signs (c : Chart) (d : Bool) (v : List Sig) := v.map (diff c d)
def once (s : List (Sig × Nat)) := let t:=mult s;t.1 ^^^ t.2
def hit (c : Chart) (sn : Nat) (z : Sig × Nat) := z.2 &&& sn &&& roof c
def marked (c : Chart) (sn : Nat) (z : Sig × Nat) : Sig × Nat :=
  let u:=hit c sn z
  (z.1,z.2 &&& sweep c.fillP u &&& sweep c.fillN u &&& roof c)
def entries (c : Chart) (d : Bool) (v : List Sig) := let s:=signs c d v;let one:=once s;s.map (marked c one)
def test (c : Chart) (d : Bool) (colors : Nat) (v : List Sig) :=
  let s:=signs c d v
  let counts:=mult s
  (counts.1 &&& roof c)==roof c && paint colors (s.map (marked c (counts.1 ^^^ counts.2))) (fun _=>0)
theorem diffBit {c : Chart} (good : good c) (d : Bool) {a : Sig} (val : Valid a) (i : Fin (area c)) :
    (diff c d a).2.testBit i.val=true ↔ DS d (positive c i) (negative c i) a := by
  have rt : (roof c).testBit i.val=true:=by rw [roofBit];exact decide_eq_true i.isLt
  cases d
  · change Nat.testBit (sweep c.spreadP a.1 &&& (roof c ^^^ sweep c.spreadN a.2)) i.val=true ↔ a.1.testBit (positive c i).val=true ∧ a.2.testBit (negative c i).val=false
    simp [Nat.testBit_and,Nat.testBit_xor,pbit good val.1,nbit good val.2,rt]
  · change Nat.testBit (sweep c.spreadP a.1 ^^^ sweep c.spreadN a.2) i.val=true ↔ a.1.testBit (positive c i).val≠a.2.testBit (negative c i).val
    simp [Nat.testBit_xor,pbit good val.1,nbit good val.2]
theorem hitBound (c : Chart) (sn : Nat) (a : Sig × Nat) : Sub (hit c sn a) (roof c) := by
  intro i hi;simp only [hit,Nat.testBit_and,Bool.and_eq_true] at hi;exact hi.2
theorem uniq {c : Chart} (good : good c) {d v} (va : ∀a∈v,Valid a) {a : Sig} (ha : a∈v) (i : Fin (area c))
    (h : (hit c (once (signs c d v)) (diff c d a)).testBit i.val=true) :
    U d (positive c i) (negative c i) v a := by
  intro b hb db
  by_contra neq
  have h1 : diff c d a ∈ signs c d v:=List.mem_map_of_mem ha
  have h2 : diff c d b ∈ signs c d v:=List.mem_map_of_mem hb
  have ne : diff c d a ≠ diff c d b:=fun e=>neq (congrArg Prod.fst e).symm
  simp only [hit,Nat.testBit_and,Bool.and_eq_true,once,Nat.testBit_xor] at h
  have first:=multiOne h1 i.val h.1.1
  have second:=multiTwo h1 h2 ne i.val h.1.1 ((diffBit good d (va b hb) i).2 db)
  simp [first,second] at h
theorem entryMark {c : Chart} (hg : good c) {d v} (va : ∀a∈v,Valid a) {a : Sig} (ha : a∈v) (i : Fin (area c))
    (h : (marked c (once (signs c d v)) (diff c d a)).2.testBit i.val=true) :
    M d (positive c i) (negative c i) v a := by
  let u:=hit c (once (signs c d v)) (diff c d a)
  simp only [marked,Nat.testBit_and,Bool.and_eq_true] at h
  let p : Fin c.h:=⟨(positive c i).val,(hg.2.2.2.2.2.1 i).1⟩
  let n : Fin c.w:=⟨(negative c i).val,(hg.2.2.2.2.2.1 i).2⟩
  have rp:=locate (linSweep _) (hg.2.2.1 i).1 (hg.2.2.2.2.2.2.1 p) (hitBound c (once (signs c d v)) (diff c d a)) h.1.1.2
  have rn:=locate (linSweep _) (hg.2.2.1 i).2 (hg.2.2.2.2.2.2.2 n) (hitBound c (once (signs c d v)) (diff c d a)) h.1.2
  refine ⟨(diffBit hg d (va a ha) i).1 h.1.1.1,?_,?_⟩
  · obtain ⟨j,hj,hp⟩:=rp
    have lim : j<area c := of_decide_eq_true (roofBit c j ▸ hitBound c _ _ j hj)
    let j' : Fin (area c):=⟨j,lim⟩
    have eq : positive c j'=positive c i:=Fin.ext (hg.2.2.2.1 j' p hp)
    exact ⟨negative c j',eq ▸ uniq hg va ha j' hj⟩
  · obtain ⟨j,hj,hn⟩:=rn
    have lim : j<area c := of_decide_eq_true (roofBit c j ▸ hitBound c _ _ j hj)
    let j' : Fin (area c):=⟨j,lim⟩
    have eq : negative c j'=negative c i:=Fin.ext (hg.2.2.2.2.1 j' n hn)
    exact ⟨positive c j',eq ▸ uniq hg va ha j' hj⟩
theorem entryIds (c d v) : (entries c d v).map Prod.fst=v := by
  simp [entries,signs,marked,diff,Function.comp_def]
theorem hasEntry {c d v a} (ha : a∈entries c d v) : a.1∈v := by
  rw [←entryIds c d v];exact List.mem_map_of_mem ha
theorem overlap {c : Chart} (hg : good c) {d v} (va : ∀a∈v,Valid a)
    {x y} (hx : x∈entries c d v) (hy : y∈entries c d v) (non : x.2 &&& y.2≠0) :
    ∃p n,M d p n v x.1 ∧ M d p n v y.1 := by
  obtain ⟨zx,ax,rfl⟩:=List.mem_map.mp hx
  obtain ⟨zy,ay,rfl⟩:=List.mem_map.mp hy
  obtain ⟨ax',av,rfl⟩:=List.mem_map.mp ax
  obtain ⟨ay',bv,rfl⟩:=List.mem_map.mp ay
  obtain ⟨j,h⟩:=Nat.exists_testBit_of_ne_zero non
  rw [Nat.testBit_and,Bool.and_eq_true] at h
  have u:=h.1
  simp only [marked,Nat.testBit_and,Bool.and_eq_true,roofBit] at u
  let i : Fin (area c):=⟨j,of_decide_eq_true u.2⟩
  exact ⟨positive c i,negative c i,entryMark hg va av i h.1,entryMark hg va bv i h.2⟩

theorem testSigned {c : Chart} (hg : good c) {k m v} (hm : m≤k) (nd : v.Nodup) (h : BL m v.toFinset) :
    test c true (k+2-v.length) v=true := by
  obtain ⟨t,l⟩:=h.expand
  have val : ∀a∈v,Valid a:=fun a ha=>(h.forms _ (List.mem_toFinset.mpr ha)).1.1
  obtain ⟨n,⟨f,bd,ok⟩,le⟩:=freeColors h
  have sz : v.toFinset.card=v.length:=List.toFinset_card_of_nodup nd
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
    rw [Nat.testBit_and,roofBit]
    by_cases hi : i<area c
    · let z : Fin (area c):=⟨i,hi⟩
      obtain ⟨a,ha,hit⟩:=pair_sep l (positive c z) (negative c z)
      have av:=List.mem_toFinset.mp ha
      have hit':=multiOne (List.mem_map_of_mem (f:=diff c true) av) i ((diffBit hg true (val a av) z).2 hit)
      simpa [hi,signs] using hit'
    · simp [hi]
  · change paint (k+2-v.length) (entries c true v) _ =true
    apply paint_ok _ f
    · rwa [entryIds]
    · intro a ha;have := bd _ (List.mem_toFinset.mpr (hasEntry ha));omega
    · simp
    · intro a ha b hb ne eq
      by_contra non
      obtain ⟨p,q,x,y⟩:=overlap hg val ha hb non
      apply ok _ (List.mem_toFinset.mpr (hasEntry ha)) _ (List.mem_toFinset.mpr (hasEntry hb)) ne _ eq
      exact ⟨p,q,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10718.Conflict1868.Unique] using x,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10718.Conflict1868.Unique] using y⟩
end QuickQ
end

open Basis1868 Free1868 FreeSearch1868 Cuts1868 Check2516 Exact8403
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_10718
open Basis1868 Free1868 Projection8403 FreeSearch1868

namespace Resource10536

lemma projectedFlip (H : SigHom) (s : Bool) {a : Sig} (valid : Valid a) {q : ℕ} {U : Finset Sig}
    (h : Projection8403.Can q ((insert (flip s a) U).image H.fn)) :
    Projection8403.Can q ((insert a U).image H.fn) := by
  cases s
  · exact h
  · exact pushNeg valid h

lemma constantFlip (H : SigHom) (s : Bool) {a : Sig} (valid : Valid a) :
    constant (H.fn (flip s a)) ↔ constant (H.fn a) := by
  cases s
  · rfl
  · change constant (H.fn (neg a)) ↔ constant (H.fn a)
    rw [H.hneg valid, constant_neg (H.valid a)]

lemma projectedBlend (H : SigHom) (d s t : Bool) {a b : Sig} (ha : Valid a) (hb : Valid b)
    {q : ℕ} {U : Finset Sig}
    (tail : Projection8403.Can q ((insert (blend d s t a b) U).image H.fn)) :
    Projection8403.Can (q + if constant (H.fn a) ∨ constant (H.fn b) then 0 else 1)
      ((insert a (insert b U)).image H.fn) := by
  let x := flip s a
  let y := flip t b
  let z := bin d x y
  have vz : Valid z := valid_bin (vf s ha) (vf t hb)
  have unflipOutput : Projection8403.Can q ((insert z U).image H.fn) :=
    projectedFlip H (sign z) vz tail
  have prev := pushBin d unflipOutput
  change Projection8403.Can
    (q + if constant (H.fn x) ∨ constant (H.fn y) then 0 else 1)
    ((insert x (insert y U)).image H.fn) at prev
  simp only [x, y, constantFlip H s ha, constantFlip H t hb] at prev
  have p := projectedFlip H s ha prev
  rw [Finset.insert_comm] at p ⊢
  exact projectedFlip H t hb p

lemma projectedBLCan (H : SigHom) {n : ℕ} {V : Finset Sig} (h : BL n V) :
    ∃ q, q + mass H V ≤ n ∧ Projection8403.Can q (V.image H.fn) := by
  obtain ⟨t, live⟩ := h.expand
  obtain ⟨q, le, projected⟩ := Projection8403.projected live H
  exact ⟨q, by omega, projected⟩

abbrev Restrictions := List (SigHom × ℕ)

def spentAt (H : SigHom) (a b : Sig) : ℕ :=
  if constant (H.fn a) ∨ constant (H.fn b) then 1 else 0

def updateLoss (rs : Restrictions) (a b : Sig) : Restrictions :=
  rs.map fun (H, u) => (H, u + spentAt H a b)

def preserve (rs : Restrictions) (elapsed : ℕ) (basis : Finset Sig) : Prop :=
  ∀ H u, (H,u) ∈ rs → ∀ q, Projection8403.Can q (basis.image H.fn) → 10 + u ≤ q + elapsed

def withinLoss (rs : Restrictions) (basis : Finset Sig) : Bool :=
  rs.all fun (H, u) => decide (u + mass H basis ≤ 1)

lemma lossOK {rs : Restrictions} {elapsed n k : ℕ} {B : Finset Sig}
    (traceBound : preserve rs elapsed B) (eq : elapsed + n = 11) (fits : k ≤ n)
    (h : BL k B) : withinLoss rs B = true := by
  apply List.all_eq_true.mpr
  rintro ⟨H,u⟩ hm
  obtain ⟨q, le, valid⟩ := projectedBLCan H h
  have lb := traceBound H u hm q valid
  exact decide_eq_true (by omega)

lemma preserveTail {rs : Restrictions} {elapsed : ℕ} {U : Finset Sig} {a b : Sig}
    (ha : Valid a) (hb : Valid b) (d s t : Bool)
    (bound : preserve rs elapsed (insert a (insert b U))) :
    preserve (updateLoss rs a b) (elapsed + 1) (insert (blend d s t a b) U) := by
  intro H w hw q h
  obtain ⟨⟨H',u⟩, hm, eq⟩ := List.mem_map.mp hw
  obtain ⟨same, lossEq⟩ := Prod.mk.inj eq
  subst H'
  have prev := projectedBlend H d s t ha hb h
  have lb := bound H u hm _ prev
  rw [← lossEq]
  unfold spentAt
  split <;> simp_all <;> omega

lemma resourceStepIndexed {rs : Restrictions} {elapsed k S} (l : BL k S) (m : ℕ) (hm : k ≤ m+1)
    (v : List Sig) (nd : v.Nodup) (rep : v.toFinset = S) (bound : preserve rs elapsed S)
    (go : Sig → Sig → List Sig → Bool)
    (hyp : ∀ a b w, w.Nodup → ∀ j ≤ m, BL j w.toFinset →
      preserve (updateLoss rs a b) (elapsed+1) w.toFinset → go a b w = true) :
    (baseTest v || scanPairs (fun a b => pairB v (go a b) a b) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr
    right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (hx : Valid x) (hy : Valid y)
        (id : blend false u w x y = z) (eqS : v.toFinset = insert x (insert y U)) :
        pairB v (go x y) x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      have pr : preserve rs elapsed (insert x (insert y U)) := by rwa [← eqS, rep]
      have pt := preserveTail hx hy false u w pr
      rw [id] at pt
      exact hyp _ _ _ nw j (by omega) (pw ▸ tail) (pw ▸ pt)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w ha.1 hb.1 id rep
    · exact yes b a w u hb.1 ha.1 ((blend_symm false w u b a).trans id)
        (by rwa [Finset.insert_comm b a])

end Resource10536

namespace FastMask10718

def covers (f : Fin 128 → Fin 128) (mask : Nat) :=
  (∀ j, mask.testBit (f j).val = true) ∧
    (∀ j, mask.testBit j = true → ∃ k : Fin 128, (f k).val = j)

lemma maskZero {f : Fin 128 → Fin 128} {m : ℕ} (h : covers f m) (v : ℕ) :
    Basis1868.reindex f v = 0 ↔ v &&& m = 0 := by
  constructor
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hm : m.testBit j
    · simp [hm]
    · obtain ⟨k, ek⟩ := h.2 j hm
      have eq := congrArg (fun a : ℕ => a.testBit k.val) he
      rw [Basis1868.reindex_testBit, dif_pos k.isLt, Nat.zero_testBit, ek] at eq
      simp [eq]
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Basis1868.reindex_testBit, Nat.zero_testBit]
    split
    · rename_i hj
      have eq := congrArg (fun a : ℕ => a.testBit (f ⟨j,hj⟩).val) he
      simpa only [Nat.testBit_and, Nat.zero_testBit, h.1, Bool.and_true] using eq
    · rfl

lemma maskOne {f : Fin 128 → Fin 128} {m : ℕ} (h : covers f m) (v : ℕ) :
    Basis1868.reindex f v = top ↔ v &&& m = m := by
  constructor
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases hm : m.testBit j
    · simp [hm]
    · obtain ⟨k, ek⟩ := h.2 j hm
      have eq := congrArg (fun a : ℕ => a.testBit k.val) he
      rw [Basis1868.reindex_testBit, dif_pos k.isLt, Basis1868.testBit_top, ek,
        decide_eq_true k.isLt] at eq
      simp [eq, hm]
  · intro he
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Basis1868.reindex_testBit, Basis1868.testBit_top]
    split
    · rename_i hj
      have eq := congrArg (fun a : ℕ => a.testBit (f ⟨j,hj⟩).val) he
      simpa only [Nat.testBit_and, h.1, Bool.and_true, decide_eq_true hj] using eq
    · rename_i hj
      simp [hj]

structure Restriction where
  p : Fin 128 → Fin 128
  n : Fin 128 → Fin 128
  pm : ℕ
  nm : ℕ
  pc : covers p pm
  nc : covers n nm

def Restriction.hom (r : Restriction) : SigHom := pairHom r.p r.n

def const (r : Restriction) (a : Sig) :=
  (a.1 &&& r.pm == 0 && a.2 &&& r.nm == 0) ||
  (a.1 &&& r.pm == r.pm && a.2 &&& r.nm == r.nm)

lemma const_eq (r : Restriction) (a : Sig) :
    const r a = decide (Projection8403.constant (r.hom.fn a)) := by
  apply Bool.eq_iff_iff.mpr
  simp [const, Projection8403.constant, Restriction.hom, pairHom, zero, one, Prod.ext_iff,
    maskZero r.pc, maskZero r.nc, maskOne r.pc, maskOne r.nc]

end FastMask10718

def sigKey (s : Sig) := s.1 * 2^128 + s.2

def insertSignal (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b :: bs => if sigKey a ≤ sigKey b then a :: b :: bs else b :: insertSignal a bs

def sortSignals : List Sig → List Sig
  | [] => []
  | a :: bs => insertSignal a (sortSignals bs)

lemma insertSignalPerm (a : Sig) (w : List Sig) : (insertSignal a w).Perm (a :: w) := by
  induction w with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : sigKey a ≤ sigKey b
    · simp [insertSignal, h]
    · exact (by simpa [insertSignal, h] using (List.Perm.cons b ih).trans (.swap a b bs))

lemma sortPerm (l : List Sig) : (sortSignals l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertSignalPerm a (sortSignals bs)).trans (.cons a ih)

lemma sortFinset (l : List Sig) : (sortSignals l).toFinset = l.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (sortPerm l).mem_iff (a := a)

lemma liveCard {n : ℕ} {S : Finset Sig} (live : BL n S) : S.card ≤ n + 1 := by
  induction live with
  | stop => simp
  | @step k U a b d s t ha hb ca cb hab fresh tail ih =>
    have hr : blend d s t a b ∉ U := by
      intro mem
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
    rw [Finset.card_insert_of_notMem hr] at ih
    have ha := Finset.card_insert_le (s := insert b U) (a := a)
    have hb := Finset.card_insert_le (s := U) (a := b)
    omega


open QuickQ ColorSearch1868 FreeSearch1868 Cuts1868
namespace PaintQ
abbrev Item:=Sig×Nat
def onePaint : List Item→Nat→Bool
  | [],_=>true
  | x::xs,a=>(a &&& x.2)==0 && onePaint xs (a ||| x.2)
def twoPaint : List Item→Nat→Nat→Bool
  | [],_,_=>true
  | x::xs,a,b=>((a &&& x.2)==0 && twoPaint xs (a ||| x.2) b) ||
        ((b &&& x.2)==0 && twoPaint xs a (b ||| x.2))
lemma oneEq (xs : List Item) (f : Nat→Nat) : paint 1 xs f=onePaint xs (f 0) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>
    simp only [paint,show List.range 1=[0] from rfl,List.any_cons,List.any_nil,Bool.or_false,ih,
      onePaint,ite_true]
lemma twoEq (xs : List Item) (f : Nat→Nat) : paint 2 xs f=twoPaint xs (f 0) (f 1) := by
  induction xs generalizing f with
  | nil=>rfl
  | cons x xs ih=>
    simp only [paint,show List.range 2=[0,1] from rfl,List.any_cons,List.any_nil,Bool.or_false,ih,
      twoPaint,ite_true,Nat.reduceEqDiff,ite_false]
def color (n : Nat) (w : List Item) := if n=1 then onePaint w 0 else if n=2 then twoPaint w 0 0 else paint n w (fun _=>0)
lemma colorEq (n : Nat) (w : List Item) : color n w=paint n w (fun _=>0) := by
  unfold color
  split
  next h=>subst n;exact (oneEq w (fun _=>0)).symm
  next=>split
        next h=>subst n;exact (twoEq w (fun _=>0)).symm
        next=>rfl
def shade (c : Chart) (once : Nat) (x : Item) : Item :=
  let h:=hit c once x
  if h=0 then (x.1,0) else (x.1,x.2 &&& sweep c.fillP h &&& sweep c.fillN h &&& roof c)
lemma shadeEq (c : Chart) (once : Nat) (x : Item) : shade c once x=marked c once x := by
  simp only [shade,marked]
  split
  next h=>rw [h,(linSweep _).1];simp
  next=>rfl
def testRows (c : Chart) (k : Nat) (s : List Item) :=
  let g:=PEqualNP.Outside.L_meta_10718.Board1868.mult s
  (g.1 &&& roof c)==roof c && color k (s.map (shade c (g.1 ^^^ g.2)))
lemma rowsMap (c d k v) : testRows c k (v.map (diff c d))=test c d k v := by
  simp only [testRows,test,signs,colorEq,funext (shadeEq _ _)]
end PaintQ

open PaintQ
namespace PackQ
def pass (c : Chart) (k : Nat) (hit : List Sig→Bool) (v : List Item) :=
  v.length≤k+1 && testRows c (k+2-v.length) v && !(hit (v.map Prod.fst))
def plain (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) :=
  v.length≤k+1 && test c d (k+2-v.length) v && !(hit v)
lemma passMap (c d k hit v) : pass c k hit (v.map (diff c d))=plain c d k hit v := by
  simp only [pass,plain,List.length_map,rowsMap,List.map_map]
  have id : Prod.fst ∘ diff c d=id:=rfl
  rw [id,List.map_id]
def selected (a b : Sig) (l r : Bool) (v : List Item) := v.filter fun x=>keep a b l r x.1
lemma selectMap (c d a b l r) (v : List Sig) :
    selected a b l r (v.map (diff c d))=(v.filter (keep a b l r)).map (diff c d) := by
  simp only [selected,List.filter_map]
  rfl
def choices (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (w : List Item) (a b z : Sig) :=
  let val:=diff c d z
  [false,true].any fun l=>[false,true].any fun r=>pass c k hit (val::selected a b l r w)
lemma choicesMap (c d k hit v a b z) : choices c d k hit (v.map (diff c d)) a b z=
    [false,true].any (fun l=>[false,true].any fun r=>plain c d k hit (next v a b z l r)) := by
  simp only [choices,selectMap,next,← List.map_cons,passMap]
def forkS (c : Chart) (k : Nat) (hit : List Sig→Bool) (ws : List Item) (v : List Sig) (a b : Item) :=
  [false,true].any fun s=>[false,true].any fun t=>
    let z:=blend false s t a.1 b.1
    z != zero && !(v.contains z) && choices c true k hit ws a.1 b.1 z
lemma forkSMap (c k hit v a b) :
    forkS c k hit (v.map (diff c true)) v (diff c true a) (diff c true b)=pairB v (plain c true k hit) a b := by
  simp only [forkS,pairB,oneB,choicesMap];rfl
lemma scanMap {α β : Type} (f : α→β) (u : β→β→Bool) (g : α→α→Bool)
    (all : ∀a b,u (f a) (f b)=g a b) (v : List α) :
    scanPairs u (v.map f)=scanPairs g v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [scanPairs,List.any_map,Function.comp_def,all,ih]
end PackQ

open PackQ
namespace GroupQ
def passes (c : Chart) (lookup : List Sig→Bool) (colors len : Nat) (rest : List Item) (g : Sig) (a : Item) :=
  let cover:=g.1 ||| a.2
  (cover &&& roof c)==roof c &&
    let one:=cover ^^^ (g.2 ||| (g.1 &&& a.2))
    color colors (shade c one a::rest.map (shade c one)) && !lookup (a.1::rest.map Prod.fst)
def arrangements (c : Chart) (k : Nat) (lookup : List Sig→Bool) (ws : List Item) (a b : Sig) (zs : List Item) :=
  [false,true].any fun l=>[false,true].any fun r=>
    let rest:=selected a b l r ws
    let m:=rest.length+1
    m≤k+1 && zs.any (passes c lookup (k+2-m) m rest (Board1868.mult rest))
lemma swapOrder {α β : Type} (xs : List α) (ys : List β) (p : α→β→Bool) :
    (xs.any fun x=>ys.any (p x))=(ys.any fun y=>xs.any (fun x=>p x y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨x,hx,y,hy,h⟩ <;> exact ⟨y,hy,x,hx,h⟩
lemma passHead (c k lookup rest a) : pass c k lookup (a::rest)=
    (rest.length+1≤k+1 && passes c lookup (k+2-(rest.length+1)) (rest.length+1) rest (Board1868.mult rest) a) := by
  simp only [pass,testRows,passes,List.length_cons,List.map_cons,Board1868.mult,Bool.and_assoc]
lemma arrangements_eq (c d k lookup ws a b) (zs : List Sig) :
    arrangements c k lookup ws a b (zs.map (diff c d))=
    zs.any (choices c d k lookup ws a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [arrangements,choices,List.any_eq_true,List.any_map,Function.comp_apply,
    passHead,Bool.and_eq_true,List.mem_map,exists_exists_and_eq_and]
  constructor
  · rintro ⟨l,hl,r,hr,bnd,z,hz,h⟩
    exact ⟨z,hz,l,hl,r,hr,bnd,h⟩
  · rintro ⟨z,hz,l,hl,r,hr,bnd,h⟩
    exact ⟨l,hl,r,hr,bnd,z,hz,h⟩
def generators (d : Bool) (a b : Sig) : List Sig :=
  if d then [false,true].flatMap (fun s=>[false,true].map (fun t=>blend false s t a b))
  else [bin false a b,bin true a b]
def fresh (d : Bool) (v : List Sig) (z : Sig) := z != zero && (d || z != one) && !(v.contains z)
def fork (c : Chart) (d : Bool) (k : Nat) (hit : List Sig→Bool) (v : List Sig) (ws : List Item) (a b : Item) :=
  let zs:=(generators d a.1 b.1).filter (fresh d v)
  arrangements c k hit ws a.1 b.1 (zs.map (diff c d))
lemma forkSEQ (c k hit v ws a b) : fork c true k hit v ws a b=forkS c k hit ws v a b := by
  simp only [fork,arrangements_eq,generators,ite_true,forkS,List.any_filter,List.any_flatMap,List.any_map,
    Function.comp_def,fresh,Bool.true_or,Bool.and_true,Bool.and_assoc]
end GroupQ

open FastMask10718 Resource10536

abbrev Loss := Nat × Nat
abbrev Env := Option (Restriction × Restriction)
abbrev Entry := Loss × List Sig

def resources (e : Env) (u : Loss) : Restrictions :=
  match e with
  | none => []
  | some (r,s) => [(r.hom,u.1),(s.hom,u.2)]

def addLoss (e : Env) (u : Loss) (a b : Sig) : Loss :=
  match e with
  | none => u
  | some (r,s) =>
    (u.1 + if const r a || const r b then 1 else 0,
     u.2 + if const s a || const s b then 1 else 0)

lemma lossStep (e : Env) (u : Loss) (a b : Sig) :
    resources e (addLoss e u a b) = updateLoss (resources e u) a b := by
  cases e with
  | none => rfl
  | some rs =>
    rcases rs with ⟨r,s⟩
    simp only [resources,addLoss,updateLoss,List.map_cons,List.map_nil,spentAt,const_eq,
      Bool.or_eq_true,decide_eq_true_eq]

def within (e : Env) (u : Loss) (w : List Sig) : Bool :=
  match e with
  | none => true
  | some (r,s) => u.1 + w.countP (const r) ≤ 1 && u.2 + w.countP (const s) ≤ 1

lemma mass_eq_count (r : Restriction) {w : List Sig} (nd : w.Nodup) :
    Projection8403.mass r.hom w.toFinset = w.countP (const r) := by
  calc
    _ = (w.filter (const r)).toFinset.card := by
      simp [Projection8403.mass, List.toFinset_filter, const_eq]
    _ = _ := by rw [List.toFinset_card_of_nodup (List.Nodup.filter _ nd), ←List.countP_eq_length_filter]

lemma within_eq (e : Env) (u : Loss) {w : List Sig} (nd : w.Nodup) :
    within e u w = withinLoss (resources e u) w.toFinset := by
  cases e with
  | none => rfl
  | some rs =>
    rcases rs with ⟨r,s⟩
    simp [within,resources,withinLoss,mass_eq_count _ nd]

def tableBucket (w : List Sig) : Nat :=
  (w.foldl (fun a s => a + s.1 + s.2) 0) % 32

def tableHit (w : Entry) (tab : Nat → List Entry) : Bool :=
  (tab (tableBucket w.2)).contains w

def levelMem (w : Entry) (tab : Nat → List Entry) : Prop :=
  ∃ b, w ∈ tab b

lemma hit_mem {w : Entry} {tab : Nat → List Entry} (h : tableHit w tab = true) :
    levelMem w tab := ⟨_, List.contains_iff_mem.mp h⟩

def absentR (c : QuickQ.Chart) (e : Env) (tab : Nat → List Entry) (n : Nat)
    (u : Loss) (w : List Sig) : Bool :=
  PackQ.plain c true n (fun v => tableHit (u,sortSignals v) tab || !within e u v) w

def testRow (c : QuickQ.Chart) (env : Env) (tab : Nat → List Entry)
    (n : Nat) (p : Entry) : Bool :=
  let ws := p.2.map (QuickQ.diff c true)
  !(baseTest p.2 || scanPairs
    (fun a b =>
      let u := addLoss env p.1 a.1 b.1
      GroupQ.fork c true n
        (fun v => tableHit (u,sortSignals v) tab || !within env u v) p.2 ws a b) ws)

lemma testRow_eq (c : QuickQ.Chart) (env : Env) (tab : Nat → List Entry)
    (n : Nat) (p : Entry) :
    testRow c env tab n p =
      !(baseTest p.2 || scanPairs (fun a b => pairB p.2
        (absentR c env tab n (addLoss env p.1 a b)) a b) p.2) := by
  dsimp only [testRow]
  rw [PackQ.scanMap]
  intro a b
  rw [GroupQ.forkSEQ]
  exact PackQ.forkSMap _ _ _ _ _ _

def verifiedR (env : Env) (cap n : Nat) (tab : Nat → List Entry) :=
  ∀ u w, levelMem (u,w) tab → w.Nodup →
    preserve (resources env u) (cap - n) w.toFinset →
    ∀ j ≤ n, ¬ BL j w.toFinset

lemma emptyR (env : Env) (cap : Nat) : verifiedR env cap 0 (fun _ => []) := by
  intro u w h
  obtain ⟨i, hi⟩ := h
  simp at hi

lemma checkedTier (c : QuickQ.Chart) (cg : QuickQ.good c) (e : Env)
    {cap n : ℕ} (fits : n + 1 ≤ cap) (fullBudget : e.isSome = true → cap = 11) {tab next : Nat → List Entry}
    (prev : verifiedR e cap n tab)
    (checked : ∀ p, levelMem p next → testRow c e tab n p = true) :
    verifiedR e cap (n+1) next := by
  intro u v hv nd bound j lj live
  have ne := testRow_eq c e tab n (u,v)
  have fail := ne ▸ checked _ hv
  have elapsed : cap-(n+1)+1 = cap-n := by omega
  have nextOK : ∀ r w, w.Nodup → ∀ k ≤ n, BL k w.toFinset →
      preserve r (cap-(n+1)+1) w.toFinset →
      ∀ a b, r = updateLoss (resources e u) a b →
        absentR c e tab n (addLoss e u a b) w = true := by
    intro r w wn k lim hw ri a b hr
    let tags := addLoss e u a b
    have hres : resources e tags = r := (lossStep e u a b).trans hr.symm
    have wp : within e tags w = true := by
      cases e with
      | none => rfl
      | some es =>
        -- The resource arithmetic uses a budget of eleven only.
        have hc : cap = 11 := fullBudget rfl
        rw [within_eq _ _ wn, hres]
        exact lossOK ri (by omega) lim hw
    have missing : tableHit (tags,sortSignals w) tab = false := by
      cases hh : tableHit (tags,sortSignals w) tab
      · rfl
      · have eq := sortFinset w
        have sorted := (sortPerm w).nodup_iff.mpr wn
        apply False.elim
        exact prev _ _ (hit_mem hh) sorted
          (by rw [eq,hres,← elapsed]; exact ri) k lim (eq.symm ▸ hw)
    have width : w.length ≤ n+1 := by
      have wc := liveCard hw
      rw [List.toFinset_card_of_nodup wn] at wc
      omega
    simp [absentR,PackQ.plain, width, QuickQ.testSigned cg lim wn hw,wp,missing,tags]
  have reach := resourceStepIndexed live n lj v nd rfl bound
    (fun a b => absentR c e tab n (addLoss e u a b))
    (fun a b w wnd k kl hw hbound => nextOK _ _ wnd k kl hw hbound a b rfl)
  change !(baseTest v || scanPairs (fun a b => pairB v
        (absentR c e tab n (addLoss e u a b)) a b) v) = true at fail
  simp [reach] at fail

def bucketOf (b : List (List Entry)) (i : ℕ) := b.getD i []

lemma bucketMem {b : List (List Entry)} {i : Nat} {w : Entry}
    (h : w ∈ bucketOf b i) : w ∈ b.flatten := by
  unfold bucketOf at h
  by_cases hi : i < b.length
  · rw [List.getD_eq_getElem b [] hi] at h
    exact List.mem_flatten.mpr ⟨b[i], List.getElem_mem hi, h⟩
  · simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)] at h

lemma checkBuckets (check : Entry → Bool) {b : List (List Entry)}
    (ok : b.all (fun xs => xs.all check) = true) :
    ∀ p, levelMem p (bucketOf b) → check p = true := by
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have eq := List.all_flatten (l := b) (f := check)
  exact List.all_eq_true.mp (eq.trans ok) p (bucketMem hi)

def coversFinite (f : Fin 128 → Fin 128) (mask : ℕ) :=
  (∀ j, mask.testBit (f j).val = true) ∧ mask ≤ top ∧
    (∀ j : Fin 128, mask.testBit j.val = true → ∃ k : Fin 128, f k = j)

lemma coversFrom {f : Fin 128 → Fin 128} {mask : ℕ} (h : coversFinite f mask) :
    covers f mask := by
  refine ⟨h.1,?_⟩
  intro j hj
  have up : j < 128 := by
    by_contra! bad
    exact Bool.noConfusion ((valid1_of_le_top h.2.1 j bad).symm.trans hj)
  obtain ⟨k,hk⟩ := h.2.2 ⟨j,up⟩ hj
  exact ⟨k,congrArg Fin.val hk⟩

lemma noCan {q : ℕ} {B : Finset Sig} {w : List Sig}
    (img : B.image can ⊆ insert zero w.toFinset) (need : necessary w)
    (no : ∀ k ≤ 9, ¬ BL k w.toFinset)
    (h : Projection8403.Can q B) : 10 ≤ q := by
  obtain ⟨k,t,S,le,l,sub⟩ := h
  obtain ⟨j,T,jle,live,sv⟩ := compress l
  have incl : T ⊆ insert zero w.toFinset :=
    (sv.trans (Finset.image_mono _ sub)).trans img
  have incl' : T ⊆ w.toFinset := by
    intro b hb
    exact (Finset.mem_insert.mp (incl hb)).resolve_left (live.forms b hb).1.2.1
  obtain ⟨a,p⟩ := live.expand
  have eq := allNeeded p incl' need
  by_contra! small
  exact no j (by omega) (eq ▸ live)

def fullRaw : List Sig := [(0x952455555554aaaaaaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75), (0xb36ecccccccd9999999b333666d9b36e,0x2c002c002c002c002c002c002c002c), (0xc38c0f0f0f0e1e1e1e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf), (0xc07cff00ff01fe01fe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0), (0xff80ffff0001fffe0003fff8001fff80,0x26002600260026002600260026002600), (0xfffffffe00000003ffffffe00000,0xb800b800b800b800b800b800b800b800), (0xfffffffffffffffc000000000000,0xc000c000c000c000c000c000c000c000)]

def chart64 : QuickQ.Chart := ⟨64,16,[(false,0,0xffffffffffffffff), (true,480,0xffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff), (true,240,0xffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff), (true,120,0xff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff), (true,60,0xf000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f), (true,30,0x300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003), (true,15,0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true,1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false,0,0xffff), (true,16,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,64,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,128,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,256,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,512,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false,1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,0,0x1000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true,1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false,16,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,64,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,128,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,256,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,512,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,0,0xffff), (true,16,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,64,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,128,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,256,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,512,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma chart64Compact : QuickQ.compactGood chart64 := by unfold QuickQ.compactGood; decide +kernel

lemma chart64Valid : QuickQ.good chart64 := QuickQ.goodOfCompact chart64Compact

def chart128 : QuickQ.Chart := ⟨128,16,[(false,0,0xffffffffffffffffffffffffffffffff), (true,960,0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff), (true,480,0xffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff), (true,240,0xffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff), (true,120,0xff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff), (true,60,0xf000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f), (true,30,0x3000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003), (true,15,0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true,1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false,0,0xffff), (true,16,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,64,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,128,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,256,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,512,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,1024,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false,1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,0,0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true,1,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,2,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,4,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false,16,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,64,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,128,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,256,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,512,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,1024,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false,0,0xffff), (true,16,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,32,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,64,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,128,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,256,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,512,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true,1024,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma chart128Compact : QuickQ.compactGood chart128 := by unfold QuickQ.compactGood; decide +kernel

lemma chart128Valid : QuickQ.good chart128 := QuickQ.goodOfCompact chart128Compact

def r0pp (j : Fin 128) : Fin 128 := Fin.ofNat 128 ((#[2, 5, 8, 10, 12, 15, 17, 19, 22, 25, 27, 29, 31, 33, 36, 38, 40, 42, 44, 46, 48, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110] : Array Nat).getD (j.val % 51) 0)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma r0ppValid : coversFinite r0pp 0x55555554aaaaaaa95552aa4a9524 := by unfold coversFinite; decide +kernel

def r0nn (j : Fin 128) : Fin 128 := Fin.ofNat 128 ((#[0, 2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15] : Array Nat).getD (j.val % 13) 0)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma r0nnValid : coversFinite r0nn 0xff75 := by unfold coversFinite; decide +kernel

def restriction0 : Restriction := ⟨r0pp,r0nn,0x55555554aaaaaaa95552aa4a9524,0xff75,coversFrom r0ppValid,coversFrom r0nnValid⟩

def r5pp (j : Fin 128) : Fin 128 := Fin.ofNat 128 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80] : Array Nat).getD (j.val % 52) 0)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma r5ppValid : coversFinite r5pp 0x1fffffffc0000001fffff := by unfold coversFinite; decide +kernel

def r5nn (j : Fin 128) : Fin 128 := Fin.ofNat 128 ((#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 14] : Array Nat).getD (j.val % 12) 0)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma r5nnValid : coversFinite r5nn 0x47ff := by unfold coversFinite; decide +kernel

def restriction5 : Restriction := ⟨r5pp,r5nn,0x1fffffffc0000001fffff,0x47ff,coversFrom r5ppValid,coversFrom r5nnValid⟩

def configured : Env := some (restriction0,restriction5)

def M0Raw : List Sig := [(0x52a51215552aaa54a242aaa5554a9448,0xfebff5ffaffd7febff5ffaffd7febff5), (0x366cb6b3336666cd96d6666cccd9b2da,0x45822c11608b045822c11608b045822c), (0x3870c703c387870e18e07870f0e1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f), (0x7f03f3fc07f80fe07e7f80ff01fc0fc,0x9804c026013009804c026013009804c0), (0x7ffc03fff8000fff807fff0001fff00,0xe01700b805c02e01700b805c02e01700), (0xf800003fffffff000007ffffffe00000,0x1800c006003001800c006003001800)]

lemma M0Need : necessary M0Raw := needFrom (pn := [(0,4), (3,6), (0,1), (2,1), (8,1), (21,1)]) (by decide) (by decide +kernel)

def M0w0 : Sig := (0x3fc07f80000007f80ff0000000,0x0)
def M0w1 : Sig := (0x3fff8000000007fff000000000,0x100080040020010008004002001000)
def M0w2 : Sig := (0x3f00007f800007e0000ff00000fc,0x1800c006003001800c006003001800c0)
def M0w3 : Sig := (0xc000000000001800000000000300,0x61e30f1878c3c61e30f1878c3c61e30f)
def M0w4 : Sig := (0x5c00000000000b800000000001700,0x67e33f19f8cfc67e33f19f8cfc67e33f)
def M0w5 : Sig := (0xfc0003f800001f80007f000003f00,0x6013009804c026013009804c02601300)
def M0w6 : Sig := (0x700703c007800e00e07800f001c01c,0x88044022011008804402201100880440)
def M0w7 : Sig := (0x703f03c07f800e07e0780ff001c0fc,0x9804c026013009804c026013009804c0)
def M0w8 : Sig := (0x70c003c380000e180078700001c300,0xe01700b805c02e01700b805c02e01700)
def M0w9 : Sig := (0x70c7000000000e18e000000001c31c,0xe9e74f3a79d3ce9e74f3a79d3ce9e74f)
def M0w10 : Sig := (0x70c703c007800e18e07800f001c31c,0xe9e74f3a79d3ce9e74f3a79d3ce9e74f)
def M0w11 : Sig := (0x190090cc01980320121980330064024,0x9804c026013009804c026013009804c0)
def M0w12 : Sig := (0x193400ccc8000326801999000064d00,0xa01500a805402a01500a805402a01500)
def M0w13 : Sig := (0x19fc00cff800033f8019ff000067f00,0xe01700b805c02e01700b805c02e01700)
def M0w14 : Sig := (0x2a01215402a80540242a805500a8048,0x9804c026013009804c026013009804c0)
def M0w15 : Sig := (0x2a03f15407f805407e2a80ff00a80fc,0x9804c026013009804c026013009804c0)
def M0w16 : Sig := (0x2a5001555000054a002aaa0000a9400,0xe01700b805c02e01700b805c02e01700)
def M0w17 : Sig := (0x2a5120000000054a2400000000a9448,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w18 : Sig := (0x2a51215402a8054a242a805500a9448,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w19 : Sig := (0x2afc0157f800055f802aff0000abf00,0xe01700b805c02e01700b805c02e01700)
def M0w20 : Sig := (0x2f01717c02f805e02e2f805f00bc05c,0x9804c026013009804c026013009804c0)
def M0w21 : Sig := (0x2f5c017d780005eb802faf0000bd700,0xe01700b805c02e01700b805c02e01700)
def M0w22 : Sig := (0x2f5d7000000005ebae00000000bd75c,0xffe7ff3ff9ffcffe7ff3ff9ffcffe7ff)
def M0w23 : Sig := (0x5502d2a805500aa05a5500aa01540b4,0x0)
def M0w24 : Sig := (0x55ac02aaa8000ab5805555000156b00,0x0)
def M0w25 : Sig := (0x60c30b0306060c18616060c0c1830c2,0x4002001000800400200100080040020)
def M0w26 : Sig := (0x6603633006600cc06c6600cc01980d8,0x0)
def M0w27 : Sig := (0x66c8033330000cd900666600019b200,0x40020010008004002001000800400200)
def M0w28 : Sig := (0x66cb680000000cd96d000000019b2da,0x45822c11608b045822c11608b045822c)
def M0w29 : Sig := (0x6703733c06780ce06e6780cf019c0dc,0x88044022011008804402201100880440)
def M0w30 : Sig := (0x780383c007800f00707800f001e00e0,0x10008004002001000800400200100080)
def M0w31 : Sig := (0x78f003c3c0000f1e0078780001e3c00,0x0)
def M0w32 : Sig := (0x78fc03c3f8000f1f80787f0001e3f00,0x6013009804c026013009804c02601300)
def M0w33 : Sig := (0x7dfc03ebe8000fbf807d7d0001f7f00,0x0)
def M0w34 : Sig := (0x7f0003fc00000fe0007f800001fc000,0x80040020010008004002001000800400)
def M0w35 : Sig := (0x7f03f00000000fe07e00000001fc0fc,0x9804c026013009804c026013009804c0)
def M0w36 : Sig := (0x7f03f03c00780fe07e07800f01fc0fc,0x9804c026013009804c026013009804c0)
def M0w37 : Sig := (0x7f03f0cc01980fe07e19803301fc0fc,0x9804c026013009804c026013009804c0)
def M0w38 : Sig := (0x7f03f15402a80fe07e2a805501fc0fc,0x9804c026013009804c026013009804c0)
def M0w39 : Sig := (0x7f03f3fc07f80fe07e7f80ff01fc0fc,0x9804c026013009804c026013009804c0)
def M0w40 : Sig := (0x7f0ff00000000fe1fe00000001fc3fc,0xf9e7cf3e79f3cf9e7cf3e79f3cf9e7cf)
def M0w41 : Sig := (0x7f0ff3fc07f80fe1fe7f80ff01fc3fc,0xf9e7cf3e79f3cf9e7cf3e79f3cf9e7cf)
def M0w42 : Sig := (0x7f53f00000000fea7e00000001fd4fc,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w43 : Sig := (0x7f53f3fc07f80fea7e7f80ff01fd4fc,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w44 : Sig := (0x7faff3feaff80ff5fe7fd5ff01febfc,0x9804c026013009804c026013009804c0)
def M0w45 : Sig := (0x7ff3f3ffc7f80ffe7e7ff8ff01ffcfc,0x9804c026013009804c026013009804c0)
def M0w46 : Sig := (0x7ffc000000000fff8000000001fff00,0xe007003801c00e007003801c00e00700)
def M0w47 : Sig := (0x7ffc0003f8000fff80007f0001fff00,0xe01700b805c02e01700b805c02e01700)
def M0w48 : Sig := (0x7ffc003c38000fff8007870001fff00,0xe01700b805c02e01700b805c02e01700)
def M0w49 : Sig := (0x7ffc00ccc8000fff8019990001fff00,0xe01700b805c02e01700b805c02e01700)
def M0w50 : Sig := (0x7ffc015550000fff802aaa0001fff00,0xe01700b805c02e01700b805c02e01700)
def M0w51 : Sig := (0x7ffc02aaa8000fff8055550001fff00,0xe007003801c00e007003801c00e00700)
def M0w52 : Sig := (0x7ffc033330000fff8066660001fff00,0xe007003801c00e007003801c00e00700)
def M0w53 : Sig := (0x7ffc03c3c0000fff8078780001fff00,0xe007003801c00e007003801c00e00700)
def M0w54 : Sig := (0x7ffc03fc00000fff807f800001fff00,0xe007003801c00e007003801c00e00700)
def M0w55 : Sig := (0x7ffc03fff8000fff807fff0001fff00,0xe01700b805c02e01700b805c02e01700)
def M0w56 : Sig := (0x7ffc03fffff80fff807fffff01fff00,0xe01700b805c02e01700b805c02e01700)
def M0w57 : Sig := (0x7ffc700000000fff8e00000001fff1c,0xe9e74f3a79d3ce9e74f3a79d3ce9e74f)
def M0w58 : Sig := (0x7ffc73fff8780fff8e7fff0f01fff1c,0xe81740ba05d02e81740ba05d02e81740)
def M0w59 : Sig := (0x7ffd200000000fffa400000001fff48,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w60 : Sig := (0x7ffed3fffd500fffda7fffaa01fffb4,0xe01700b805c02e01700b805c02e01700)
def M0w61 : Sig := (0x7fff63fffe600fffec7fffcc01fffd8,0xe01700b805c02e01700b805c02e01700)
def M0w62 : Sig := (0x7ffff3fffff80ffffe7fffff01ffffc,0xf817c0be05f02f817c0be05f02f817c0)
def M0w63 : Sig := (0x8104100c08181020820181030204104,0xa87d43ea1f50fa87d43ea1f50fa87d43)
def M0w64 : Sig := (0x870c700c081810e18e018103021c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w65 : Sig := (0x990490cc09981320921981330264124,0xb87dc3ee1f70fb87dc3ee1f70fb87dc3)
def M0w66 : Sig := (0x10000000010002000000002000400000,0x60bb05d82ec1760bb05d82ec1760bb05)
def M0w67 : Sig := (0x10200200010002040040002000408008,0xe8bf45fa2fd17e8bf45fa2fd17e8bf45)
def M0w68 : Sig := (0x10200201410282040040282050408008,0xe8bf45fa2fd17e8bf45fa2fd17e8bf45)
def M0w69 : Sig := (0x1070c7014102820e18e028205041c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w70 : Sig := (0x12241211112222448242222444489048,0x44822411208904482241120890448224)
def M0w71 : Sig := (0x12a5120141028254a2402820504a9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w72 : Sig := (0x12a5121111222254a2422224444a9448,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w73 : Sig := (0x162c32b1316262c58656262c4c58b0ca,0x44822411208904482241120890448224)
def M0w74 : Sig := (0x16643633116622cc86c6622cc45990d8,0x44822411208904482241120890448224)
def M0w75 : Sig := (0x166c9233332222cd924666644459b248,0x44822411208904482241120890448224)
def M0w76 : Sig := (0x166cb691112222cd96d222244459b2da,0x45822c11608b045822c11608b045822c)
def M0w77 : Sig := (0x17ffc23fff8282fff847fff0505fff08,0xe8bf45fa2fd17e8bf45fa2fd17e8bf45)
def M0w78 : Sig := (0x2448a4a2224444891494444888912292,0x1000800400200100080040020010008)
def M0w79 : Sig := (0x2850c5028285050a18a05050a0a14314,0x1400a005002801400a005002801400a)
def M0w80 : Sig := (0x2870c7028285050e18e05050a0a1c31c,0xe9e74f3a79d3ce9e74f3a79d3ce9e74f)
def M0w81 : Sig := (0x2870c703c287850e18e07850f0a1c31c,0x89444a225112889444a225112889444a)
def M0w82 : Sig := (0x2ff0ff3fc2ff85fe1fe7f85ff0bfc3fc,0x9944ca26513289944ca26513289944ca)
def M0w83 : Sig := (0x30000033336666000006666cccc00000,0x0)
def M0w84 : Sig := (0x300036800066660006d0000cccc000da,0x5802c01600b005802c01600b005802c)
def M0w85 : Sig := (0x300c808033006601901006600cc03202,0x45822c11608b045822c11608b045822c)
def M0w86 : Sig := (0x306086030306060c10c06060c0c18218,0x41820c106083041820c106083041820c)
def M0w87 : Sig := (0x3060b6830366660c16d0606cccc182da,0x45822c11608b045822c11608b045822c)
def M0w88 : Sig := (0x3070c7030306060e18e06060c0c1c31c,0xe9e74f3a79d3ce9e74f3a79d3ce9e74f)
def M0w89 : Sig := (0x32241233336666448246666cccc89048,0x44822411208904482241120890448224)
def M0w90 : Sig := (0x322436911166664486d2222cccc890da,0x45822c11608b045822c11608b045822c)
def M0w91 : Sig := (0x322c929133226645925226644cc8b24a,0x45822c11608b045822c11608b045822c)
def M0w92 : Sig := (0x326496131326264c92c26264c4c99258,0x45822c11608b045822c11608b045822c)
def M0w93 : Sig := (0x36603633336666cc06c6666cccd980d8,0x0)
def M0w94 : Sig := (0x3660b633036606cc16c6606cc0d982d8,0x41820c106083041820c106083041820c)
def M0w95 : Sig := (0x366cb680330066cd96d006600cd9b2da,0x45822c11608b045822c11608b045822c)
def M0w96 : Sig := (0x366cb683030606cd96d06060c0d9b2da,0x45822c11608b045822c11608b045822c)
def M0w97 : Sig := (0x366cb6b3336666cd96d6666cccd9b2da,0x45822c11608b045822c11608b045822c)
def M0w98 : Sig := (0x366cb6bff37fe6cd96d7fe6ffcd9b2da,0x45822c11608b045822c11608b045822c)
def M0w99 : Sig := (0x377cbfbbb37766ef97f7766eecddf2fe,0x45822c11608b045822c11608b045822c)
def M0w100 : Sig := (0x377ef6bbbbe666efded7777cccddfbda,0x45822c11608b045822c11608b045822c)
def M0w101 : Sig := (0x37efb6bf3f6666fdf6d7e7ecccdfbeda,0x45822c11608b045822c11608b045822c)
def M0w102 : Sig := (0x37f03f3ff37fe6fe07e7fe6ffcdfc0fc,0x9804c026013009804c026013009804c0)
def M0w103 : Sig := (0x37fcbfbff37fe6ff97f7fe6ffcdff2fe,0xdd86ec3761bb0dd86ec3761bb0dd86ec)
def M0w104 : Sig := (0x37ffc03fffe666fff807fffcccdfff00,0xe01700b805c02e01700b805c02e01700)
def M0w105 : Sig := (0x37fff6bfffe666fffed7fffcccdfffda,0xe5972cb965cb2e5972cb965cb2e5972c)
def M0w106 : Sig := (0x38000003c387870000007870f0e00000,0x1800c006003001800c006003001800)
def M0w107 : Sig := (0x380007000007870000e00000f0e0001c,0x9e84f427a13d09e84f427a13d09e84f)
def M0w108 : Sig := (0x3800c000038007001800007000e00300,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w109 : Sig := (0x3800c003c387870018007870f0e00300,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w110 : Sig := (0x380cc08033806701981006700ce03302,0x65fb2fd97ecbf65fb2fd97ecbf65fb2f)
def M0w111 : Sig := (0x380fc0003f800701f80007f000e03f00,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w112 : Sig := (0x3810c100c38187021820187030e04304,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w113 : Sig := (0x382007014107870400e02820f0e0801c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w114 : Sig := (0x3820c201438287041840287050e08308,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w115 : Sig := (0x3850c5028385070a18a05070a0e14314,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w116 : Sig := (0x3850c503c387870a18a07870f0e14314,0x1580ac05602b01580ac05602b01580a)
def M0w117 : Sig := (0x3860c6030386070c18c06070c0e18318,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w118 : Sig := (0x3870c003c380070e1800787000e1c300,0xe1ff0ff87fc3fe1ff0ff87fc3fe1ff0f)
def M0w119 : Sig := (0x3870c7000380070e18e0007000e1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w120 : Sig := (0x3870c7038387070e18e07070e0e1c31c,0x41c20e107083841c20e107083841c20e)
def M0w121 : Sig := (0x3870c703c387870e18e07870f0e1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w122 : Sig := (0x3870c733f3e7e70e18e67e7cfce1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w123 : Sig := (0x3870c73fc3ff870e18e7f87ff0e1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w124 : Sig := (0x3870ff03c3ff870e1fe0787ff0e1c3fc,0xf9ffcffe7ff3ff9ffcffe7ff3ff9ffcf)
def M0w125 : Sig := (0x3d70ef2bc3d787ae1de5787af0f5c3bc,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w126 : Sig := (0x3d7ac72beb8787af58e57d70f0f5eb1c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w127 : Sig := (0x3e70f733c3e787ce1ee6787cf0f9c3dc,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w128 : Sig := (0x3e7cf7b3b3e767cf9ef6767cecf9f3de,0x45c22e11708b845c22e11708b845c22e)
def M0w129 : Sig := (0x3e7cf7b3f3e7e7cf9ef67e7cfcf9f3de,0xedff6ffb7fdbfedff6ffb7fdbfedff6f)
def M0w130 : Sig := (0x3ff0ff3fc3ff87fe1fe7f87ff0ffc3fc,0xf9ffcffe7ff3ff9ffcffe7ff3ff9ffcf)
def M0w131 : Sig := (0x3fffc03fff8787fff807fff0f0ffff00,0xe01f00f807c03e01f00f807c03e01f00)
def M0w132 : Sig := (0x3fffc73fff8787fff8e7fff0f0ffff1c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w133 : Sig := (0x40810004440888102000888111020400,0xba3dd1ee8f747ba3dd1ee8f747ba3dd1)
def M0w134 : Sig := (0x4085000444088810a000888111021400,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w135 : Sig := (0x4191090cc41988322121988331064424,0xba3dd1ee8f747ba3dd1ee8f747ba3dd1)
def M0w136 : Sig := (0x4193400ccc8888326801999111064d00,0xba3dd1ee8f747ba3dd1ee8f747ba3dd1)
def M0w137 : Sig := (0x4285101414282850a2028285050a1440,0x1600b005802c01600b005802c01600b0)
def M0w138 : Sig := (0x428510145428a850a2028a85150a1440,0xbe3df1ef8f7c7be3df1ef8f7c7be3df1)
def M0w139 : Sig := (0x42a5120444088854a2408881110a9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w140 : Sig := (0x42a5121414282854a2428285050a9448,0xfea7f53fa9fd4fea7f53fa9fd4fea7f5)
def M0w141 : Sig := (0x42a51215542aa854a242aa85550a9448,0x9e04f027813c09e04f027813c09e04f0)
def M0w142 : Sig := (0x47f53f3fd47fa8fea7e7fa8ff51fd4fc,0x9e04f027813c09e04f027813c09e04f0)
def M0w143 : Sig := (0x48914104c48989122820989131224504,0xba7dd3ee9f74fba7dd3ee9f74fba7dd3)
def M0w144 : Sig := (0x50000015552aaa000002aaa555400000,0x1800c006003001800c006003001800)
def M0w145 : Sig := (0x50001200002aaa000240000555400048,0x1ea8f547aa3d51ea8f547aa3d51ea8f5)
def M0w146 : Sig := (0x5005000015002a00a00002a005401400,0x66bb35d9aecd766bb35d9aecd766bb35)
def M0w147 : Sig := (0x50050015552aaa00a002aaa555401400,0x66bb35d9aecd766bb35d9aecd766bb35)
def M0w148 : Sig := (0x500fc0003f802a01f80007f005403f00,0x66bb35d9aecd766bb35d9aecd766bb35)
def M0w149 : Sig := (0x50201201412aaa040240282555408048,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w150 : Sig := (0x508500045508aa10a0008aa115421400,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w151 : Sig := (0x5225121115222a44a24222a445489448,0x66bb35d9aecd766bb35d9aecd766bb35)
def M0w152 : Sig := (0x5285101415282a50a20282a5054a1440,0x76bbb5ddaeed776bbb5ddaeed776bbb5)
def M0w153 : Sig := (0x52851015552aaa50a202aaa5554a1440,0x1618b0c5862c31618b0c5862c31618b0)
def M0w154 : Sig := (0x52a5120015002a54a24002a0054a9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w155 : Sig := (0x52a51215552aaa54a242aaa5554a9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w156 : Sig := (0x52a5123fd57faa54a247faaff54a9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w157 : Sig := (0x56e53637556eaadca6c6eaadd55b94d8,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w158 : Sig := (0x57af123d7d2aaaf5e247afa5555ebc48,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w159 : Sig := (0x57f53f3fd57faafea7e7faaff55fd4fc,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w160 : Sig := (0x57ffc03fffaaaafff807fff5555fff00,0xe01f00f807c03e01f00f807c03e01f00)
def M0w161 : Sig := (0x57ffd23fffaaaafffa47fff5555fff48,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w162 : Sig := (0x72a51237776eee54a246eeedddca9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w163 : Sig := (0x76edb6b7776eeeddb6d6eeeddddbb6da,0xffbffdffefff7ffbffdffefff7ffbffd)
def M0w164 : Sig := (0x78000017d7afaf000002faf5f5e00000,0x1800c006003001800c006003001800)
def M0w165 : Sig := (0x78001700002faf0002e00005f5e0005c,0x1fe8ff47fa3fd1fe8ff47fa3fd1fe8ff)
def M0w166 : Sig := (0x7805c00017802f00b80002f005e01700,0x67fb3fd9fecff67fb3fd9fecff67fb3f)
def M0w167 : Sig := (0x7af5d717d7afaf5ebae2faf5f5ebd75c,0xffffffffffffffffffffffffffffffff)
def M0w168 : Sig := (0xa800002aaad555000005555aaaa00000,0x0)
def M0w169 : Sig := (0xaff03f3feaffd5fe07e7fd5ffabfc0fc,0x9804c026013009804c026013009804c0)
def M0w170 : Sig := (0xafffc03fffd555fff807fffaaabfff00,0xe01700b805c02e01700b805c02e01700)
def M0w171 : Sig := (0xb870c72bebd7d70e18e57d7afae1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w172 : Sig := (0xbe6cb6bbbbf777cd96d7777eeef9b2da,0x45822c11608b045822c11608b045822c)
def M0w173 : Sig := (0xc000003c3c7878000007878f0f000000,0x0)
def M0w174 : Sig := (0xc7f03f3ffc7ff8fe07e7ff8fff1fc0fc,0x9804c026013009804c026013009804c0)
def M0w175 : Sig := (0xc7ffc03ffff878fff807ffff0f1fff00,0xe01700b805c02e01700b805c02e01700)
def M0w176 : Sig := (0xc800000ccc9999000001999333200000,0x1800c006003001800c006003001800)
def M0w177 : Sig := (0xc881000ccc9999102001999333220400,0xba3dd1ee8f747ba3dd1ee8f747ba3dd1)
def M0w178 : Sig := (0xc990090ccc9999320121999333264024,0x981cc0e607303981cc0e607303981cc0)
def M0w179 : Sig := (0xcfffc03fff9999fff807fff3333fff00,0xe01f00f807c03e01f00f807c03e01f00)
def M0w180 : Sig := (0xd2a5123d7d7afa54a247afaf5f4a9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w181 : Sig := (0xf66cb6bf3f7e7ecd96d7e7efcfd9b2da,0x45822c11608b045822c11608b045822c)
def M0w182 : Sig := (0xf8000000007fff000000000fffe00000,0x80040020010008004002001000800)
def M0w183 : Sig := (0xf80000003f807f00000007f00fe00000,0x1800c006003001800c006003001800)
def M0w184 : Sig := (0xf8000003c3ffff000000787fffe00000,0x1800c006003001800c006003001800)
def M0w185 : Sig := (0xf800000cff99ff0000019ff33fe00000,0x1800c006003001800c006003001800)
def M0w186 : Sig := (0xf8000015557fff000002aaafffe00000,0x1800c006003001800c006003001800)
def M0w187 : Sig := (0xf80000157faaff000002aff55fe00000,0x1800c006003001800c006003001800)
def M0w188 : Sig := (0xf800003fffffff000007ffffffe00000,0x1800c006003001800c006003001800)
def M0w189 : Sig := (0xf800c0003f807f00180007f00fe00300,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w190 : Sig := (0xf800c03fffffff001807ffffffe00300,0x61fb0fd87ec3f61fb0fd87ec3f61fb0f)
def M0w191 : Sig := (0xf80500003f807f00a00007f00fe01400,0x66bb35d9aecd766bb35d9aecd766bb35)
def M0w192 : Sig := (0xf805003fffffff00a007ffffffe01400,0x66bb35d9aecd766bb35d9aecd766bb35)
def M0w193 : Sig := (0xf80fc0003f807f01f80007f00fe03f00,0x601b00d806c03601b00d806c03601b00)
def M0w194 : Sig := (0xf80fc03fffffff01f807ffffffe03f00,0x601b00d806c03601b00d806c03601b00)
def M0w195 : Sig := (0xf850c53fffffff0a18a7ffffffe14314,0x1580ac05602b01580ac05602b01580a)
def M0w196 : Sig := (0xf870c73fffffff0e18e7ffffffe1c31c,0xe9ff4ffa7fd3fe9ff4ffa7fd3fe9ff4f)
def M0w197 : Sig := (0xfa85103fffffff50a207ffffffea1440,0x1618b0c5862c31618b0c5862c31618b0)
def M0w198 : Sig := (0xfaa5123fffffff54a247ffffffea9448,0xfebff5ffaffd7febff5ffaffd7febff5)
def M0w199 : Sig := (0xfd502d3fffffffaa05a7fffffff540b4,0x1800c006003001800c006003001800)
def M0w200 : Sig := (0xfd5ac03fffffffab5807fffffff56b00,0x1800c006003001800c006003001800)
def M0w201 : Sig := (0xfe60363fffffffcc06c7fffffff980d8,0x1800c006003001800c006003001800)
def M0w202 : Sig := (0xfe6cb6bfffffffcd96d7fffffff9b2da,0x459a2cd1668b3459a2cd1668b3459a2c)
def M0w203 : Sig := (0xff8f003ffffffff1e007fffffffe3c00,0x1800c006003001800c006003001800)
def M0w204 : Sig := (0xffdfc03ffffffffbf807ffffffff7f00,0x1800c006003001800c006003001800)
def M0w205 : Sig := (0xfff03f3ffffffffe07e7ffffffffc0fc,0x981cc0e607303981cc0e607303981cc0)
def M0w206 : Sig := (0xffffc03fff807ffff807fff00fffff00,0xe01f00f807c03e01f00f807c03e01f00)
def M0w207 : Sig := (0xffffc03ffffffffff807ffffffffff00,0xe01f00f807c03e01f00f807c03e01f00)
def M0t0 : Nat → List Entry := fun _ => []

lemma M0v0 : verifiedR none 9 0 M0t0 := emptyR _ _

def M0g1 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t1 : Nat → List Entry := bucketOf M0g1
lemma M0v1 : verifiedR none 9 1 M0t1 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v0
  apply checkBuckets
  simp only [M0g1, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M0g2 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t2 : Nat → List Entry := bucketOf M0g2
lemma M0v2 : verifiedR none 9 2 M0t2 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v1
  apply checkBuckets
  simp only [M0g2, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M0g3 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t3 : Nat → List Entry := bucketOf M0g3
lemma M0v3 : verifiedR none 9 3 M0t3 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v2
  apply checkBuckets
  simp only [M0g3, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M0g4 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t4 : Nat → List Entry := bucketOf M0g4
lemma M0v4 : verifiedR none 9 4 M0t4 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v3
  apply checkBuckets
  simp only [M0g4, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M0p5b16c0 : List Entry := [((0,0),[M0w17,M0w55,M0w82,M0w97,M0w121,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p5b16c0Ok : M0p5b16c0.all (testRow chart64 none M0t4 4) = true := by decide +kernel

def M0p5b16 : List Entry := M0p5b16c0
def M0p5b23c0 : List Entry := [((0,0),[M0w10,M0w17,M0w39,M0w55,M0w68,M0w97])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p5b23c0Ok : M0p5b23c0.all (testRow chart64 none M0t4 4) = true := by decide +kernel

def M0p5b23 : List Entry := M0p5b23c0
def M0p5b27c0 : List Entry := [((0,0),[M0w17,M0w55,M0w68,M0w97,M0w108,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p5b27c0Ok : M0p5b27c0.all (testRow chart64 none M0t4 4) = true := by decide +kernel

def M0p5b27 : List Entry := M0p5b27c0
def M0g5 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], M0p5b16, [], [], [], [], [], [], M0p5b23, [], [], [], M0p5b27, [], [], [], []]
def M0t5 : Nat → List Entry := bucketOf M0g5
lemma M0v5 : verifiedR none 9 5 M0t5 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v4
  apply checkBuckets
  simp only [M0g5, M0p5b16, M0p5b23, M0p5b27, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p5b16c0Ok, M0p5b23c0Ok, M0p5b27c0Ok]

def M0p6b0c0 : List Entry := [((0,0),[M0w9,M0w17,M0w39,M0w55,M0w121,M0w133]),
((0,0),[M0w55,M0w108,M0w121,M0w133,M0w146,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b0c0Ok : M0p6b0c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b0 : List Entry := M0p6b0c0
def M0p6b1c0 : List Entry := [((0,0),[M0w22,M0w39,M0w55,M0w97,M0w121,M0w155,M0w205]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w165,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b1c0Ok : M0p6b1c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b1 : List Entry := M0p6b1c0
def M0p6b3c0 : List Entry := [((0,0),[M0w39,M0w55,M0w59,M0w97,M0w121,M0w155,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b3c0Ok : M0p6b3c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b3 : List Entry := M0p6b3c0
def M0p6b4c0 : List Entry := [((0,0),[M0w4,M0w22,M0w39,M0w55,M0w97,M0w121,M0w155]),
((0,0),[M0w17,M0w39,M0w55,M0w79,M0w97,M0w121,M0w205]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w195,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b4c0Ok : M0p6b4c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b4 : List Entry := M0p6b4c0
def M0p6b7c0 : List Entry := [((0,0),[M0w39,M0w55,M0w59,M0w97,M0w121,M0w155,M0w183])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b7c0Ok : M0p6b7c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b7 : List Entry := M0p6b7c0
def M0p6b8c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w79,M0w97,M0w121,M0w183]),
((0,0),[M0w18,M0w39,M0w55,M0w79,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w72,M0w79,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w183,M0w195])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b8c0Ok : M0p6b8c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b8 : List Entry := M0p6b8c0
def M0p6b10c0 : List Entry := [((0,0),[M0w9,M0w17,M0w39,M0w55,M0w97,M0w121,M0w146]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w188,M0w204]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w204])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b10c0Ok : M0p6b10c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b10 : List Entry := M0p6b10c0
def M0p6b16c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w82,M0w97,M0w121,M0w188]),
((0,0),[M0w55,M0w82,M0w97,M0w121,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b16c0Ok : M0p6b16c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b16 : List Entry := M0p6b16c0
def M0p6b18c0 : List Entry := [((0,0),[M0w9,M0w55,M0w97,M0w108,M0w146,M0w155,M0w188]),
((0,0),[M0w10,M0w17,M0w39,M0w55,M0w97,M0w121,M0w155]),
((0,0),[M0w55,M0w97,M0w108,M0w121,M0w147,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b18c0Ok : M0p6b18c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b18 : List Entry := M0p6b18c0
def M0p6b19c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w68,M0w97,M0w121,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b19c0Ok : M0p6b19c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b19 : List Entry := M0p6b19c0
def M0p6b21c0 : List Entry := [((0,0),[M0w17,M0w39,M0w121,M0w133,M0w207])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b21c0Ok : M0p6b21c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b21 : List Entry := M0p6b21c0
def M0p6b22c0 : List Entry := [((0,0),[M0w17,M0w55,M0w97,M0w108,M0w121,M0w155,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b22c0Ok : M0p6b22c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b22 : List Entry := M0p6b22c0
def M0p6b23c0 : List Entry := [((0,0),[M0w9,M0w17,M0w39,M0w55,M0w68,M0w97]),
((0,0),[M0w10,M0w39,M0w55,M0w68,M0w97,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w55,M0w68,M0w97,M0w121,M0w183]),
((0,0),[M0w18,M0w39,M0w55,M0w68,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w67,M0w97,M0w121,M0w154,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w72,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w88,M0w97,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w97,M0w121,M0w154,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b23c0Ok : M0p6b23c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b23c1 : List Entry := [((0,0),[M0w39,M0w55,M0w68,M0w98,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b23c1Ok : M0p6b23c1.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b23 : List Entry := M0p6b23c0 ++ M0p6b23c1
def M0p6b25c0 : List Entry := [((0,0),[M0w9,M0w39,M0w97,M0w108,M0w155,M0w207]),
((0,0),[M0w39,M0w55,M0w121,M0w134,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b25c0Ok : M0p6b25c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b25 : List Entry := M0p6b25c0
def M0p6b27c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w68,M0w97,M0w108,M0w188]),
((0,0),[M0w35,M0w55,M0w68,M0w97,M0w108,M0w155,M0w188]),
((0,0),[M0w55,M0w68,M0w97,M0w108,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b27c0Ok : M0p6b27c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b27 : List Entry := M0p6b27c0
def M0p6b28c0 : List Entry := [((0,0),[M0w39,M0w55,M0w121,M0w134,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b28c0Ok : M0p6b28c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b28 : List Entry := M0p6b28c0
def M0p6b30c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w108,M0w155,M0w188,M0w197]),
((0,0),[M0w55,M0w97,M0w108,M0w137,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b30c0Ok : M0p6b30c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b30 : List Entry := M0p6b30c0
def M0p6b31c0 : List Entry := [((0,0),[M0w17,M0w39,M0w97,M0w121,M0w146,M0w207]),
((0,0),[M0w17,M0w55,M0w97,M0w121,M0w146,M0w205]),
((0,0),[M0w55,M0w97,M0w121,M0w148,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p6b31c0Ok : M0p6b31c0.all (testRow chart64 none M0t5 5) = true := by decide +kernel

def M0p6b31 : List Entry := M0p6b31c0
def M0g6 : List (List Entry) := [M0p6b0, M0p6b1, [], M0p6b3, M0p6b4, [], [], M0p6b7, M0p6b8, [], M0p6b10, [], [], [], [], [], M0p6b16, [], M0p6b18, M0p6b19, [], M0p6b21, M0p6b22, M0p6b23, [], M0p6b25, [], M0p6b27, M0p6b28, [], M0p6b30, M0p6b31]
def M0t6 : Nat → List Entry := bucketOf M0g6
lemma M0v6 : verifiedR none 9 6 M0t6 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v5
  apply checkBuckets
  simp only [M0g6, M0p6b0, M0p6b1, M0p6b3, M0p6b4, M0p6b7, M0p6b8, M0p6b10, M0p6b16, M0p6b18, M0p6b19, M0p6b21, M0p6b22, M0p6b23, M0p6b25, M0p6b27, M0p6b28, M0p6b30, M0p6b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p6b0c0Ok, M0p6b1c0Ok, M0p6b3c0Ok, M0p6b4c0Ok, M0p6b7c0Ok, M0p6b8c0Ok, M0p6b10c0Ok, M0p6b16c0Ok, M0p6b18c0Ok, M0p6b19c0Ok, M0p6b21c0Ok, M0p6b22c0Ok, M0p6b23c0Ok, M0p6b23c1Ok, M0p6b25c0Ok, M0p6b27c0Ok, M0p6b28c0Ok, M0p6b30c0Ok, M0p6b31c0Ok]

def M0p7b0c0 : List Entry := [((0,0),[M0w9,M0w39,M0w55,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w74,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b0c0Ok : M0p7b0c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b0 : List Entry := M0p7b0c0
def M0p7b1c0 : List Entry := [((0,0),[M0w39,M0w55,M0w68,M0w97,M0w103,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w70,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w167,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b1c0Ok : M0p7b1c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b1 : List Entry := M0p7b1c0
def M0p7b2c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w141,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w150,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w201]),
((0,0),[M0w39,M0w61,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b2c0Ok : M0p7b2c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b2 : List Entry := M0p7b2c0
def M0p7b3c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w97,M0w121,M0w155,M0w205]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w145,M0w155,M0w188,M0w205]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w161,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b3c0Ok : M0p7b3c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b3 : List Entry := M0p7b3c0
def M0p7b4c0 : List Entry := [((0,0),[M0w39,M0w55,M0w70,M0w121,M0w133,M0w188]),
((0,0),[M0w39,M0w55,M0w79,M0w97,M0w121,M0w155,M0w188,M0w205]),
((0,0),[M0w39,M0w55,M0w108,M0w121,M0w133,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b4c0Ok : M0p7b4c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b4 : List Entry := M0p7b4c0
def M0p7b5c0 : List Entry := [((0,0),[M0w14,M0w55,M0w97,M0w108,M0w121,M0w155,M0w188]),
((0,0),[M0w22,M0w39,M0w55,M0w97,M0w121,M0w155]),
((0,0),[M0w22,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w70,M0w121,M0w146,M0w155,M0w188]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w165,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b5c0Ok : M0p7b5c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b5 : List Entry := M0p7b5c0
def M0p7b6c0 : List Entry := [((0,0),[M0w39,M0w58,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b6c0Ok : M0p7b6c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b6 : List Entry := M0p7b6c0
def M0p7b7c0 : List Entry := [((0,0),[M0w17,M0w39,M0w46,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w55,M0w97,M0w106,M0w121,M0w155]),
((0,0),[M0w17,M0w39,M0w55,M0w97,M0w121,M0w155,M0w183]),
((0,0),[M0w17,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w97,M0w121,M0w155,M0w188,M0w207]),
((0,0),[M0w17,M0w39,M0w97,M0w121,M0w155,M0w207]),
((0,0),[M0w18,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w59,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c0Ok : M0p7b7c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b7c1 : List Entry := [((0,0),[M0w39,M0w55,M0w72,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w139,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w140,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w145,M0w155,M0w176,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w145,M0w155,M0w183,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w151,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w154,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w161,M0w176,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c1Ok : M0p7b7c1.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b7c2 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w161,M0w183,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b7c2Ok : M0p7b7c2.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b7 : List Entry := M0p7b7c0 ++ M0p7b7c1 ++ M0p7b7c2
def M0p7b8c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w79,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w79,M0w97,M0w121,M0w155,M0w176,M0w188]),
((0,0),[M0w39,M0w55,M0w79,M0w97,M0w121,M0w155,M0w183,M0w188]),
((0,0),[M0w39,M0w55,M0w92,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w94,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w116,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w195]),
((0,0),[M0w39,M0w55,M0w121,M0w155,M0w178,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b8c0Ok : M0p7b8c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b8 : List Entry := M0p7b8c0
def M0p7b9c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w166,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w133,M0w159,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b9c0Ok : M0p7b9c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b9 : List Entry := M0p7b9c0
def M0p7b10c0 : List Entry := [((0,0),[M0w5,M0w39,M0w97,M0w121,M0w155,M0w188,M0w207]),
((0,0),[M0w7,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w9,M0w39,M0w55,M0w97,M0w121,M0w146,M0w155,M0w188]),
((0,0),[M0w13,M0w39,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w15,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w19,M0w39,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w20,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w21,M0w39,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c0Ok : M0p7b10c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c1 : List Entry := [((0,0),[M0w29,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w32,M0w39,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w33,M0w39,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w36,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w37,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w38,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w97,M0w121,M0w155,M0w188,M0w207])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c1Ok : M0p7b10c1.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c2 : List Entry := [((0,0),[M0w39,M0w46,M0w97,M0w121,M0w155,M0w207]),
((0,0),[M0w39,M0w47,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w48,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w49,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w50,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w51,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w52,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w53,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c2Ok : M0p7b10c2.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c3 : List Entry := [((0,0),[M0w39,M0w54,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w64,M0w97,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w69,M0w97,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w71,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w76,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w87,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w90,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w95,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c3Ok : M0p7b10c3.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c4 : List Entry := [((0,0),[M0w39,M0w55,M0w96,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w113,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w119,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w139,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w149,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w154,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w164]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w184])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c4Ok : M0p7b10c4.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c5 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w185]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w186]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w187]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w193]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w194]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w200]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w203]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w200])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c5Ok : M0p7b10c5.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c6 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w203]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w156,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w158,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w162,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w180,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w122,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w123,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w124,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c6Ok : M0p7b10c6.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c7 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w125,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w126,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w127,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w155,M0w171,M0w188]),
((0,0),[M0w39,M0w55,M0w98,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w100,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w101,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w133,M0w146,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c7Ok : M0p7b10c7.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c8 : List Entry := [((0,0),[M0w39,M0w55,M0w121,M0w155,M0w172,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w155,M0w181,M0w188]),
((0,0),[M0w39,M0w56,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w97,M0w104,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w97,M0w106,M0w121,M0w155,M0w207]),
((0,0),[M0w39,M0w97,M0w121,M0w131,M0w155,M0w188]),
((0,0),[M0w39,M0w97,M0w121,M0w144,M0w155,M0w207]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w160,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c8Ok : M0p7b10c8.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c9 : List Entry := [((0,0),[M0w39,M0w97,M0w121,M0w155,M0w170,M0w188]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w175,M0w188]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w179,M0w188]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w188,M0w193,M0w207]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w188,M0w206]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w188,M0w207]),
((0,0),[M0w44,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w45,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c9Ok : M0p7b10c9.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10c10 : List Entry := [((0,0),[M0w55,M0w97,M0w102,M0w121,M0w155,M0w188]),
((0,0),[M0w55,M0w97,M0w121,M0w155,M0w169,M0w188]),
((0,0),[M0w55,M0w97,M0w121,M0w155,M0w174,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b10c10Ok : M0p7b10c10.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b10 : List Entry := M0p7b10c0 ++ M0p7b10c1 ++ M0p7b10c2 ++ M0p7b10c3 ++ M0p7b10c4 ++ M0p7b10c5 ++ M0p7b10c6 ++ M0p7b10c7 ++ M0p7b10c8 ++ M0p7b10c9 ++ M0p7b10c10
def M0p7b11c0 : List Entry := [((0,0),[M0w39,M0w55,M0w65,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b11c0Ok : M0p7b11c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b11 : List Entry := M0p7b11c0
def M0p7b13c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w70,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w115,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w145,M0w155,M0w188,M0w202]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w161,M0w188,M0w202]),
((0,0),[M0w39,M0w55,M0w121,M0w133,M0w146,M0w188]),
((0,0),[M0w55,M0w97,M0w121,M0w155,M0w166,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b13c0Ok : M0p7b13c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b13 : List Entry := M0p7b13c0
def M0p7b14c0 : List Entry := [((0,0),[M0w39,M0w55,M0w79,M0w97,M0w121,M0w155,M0w188,M0w202]),
((0,0),[M0w39,M0w55,M0w97,M0w118,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w99,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b14c0Ok : M0p7b14c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b14 : List Entry := M0p7b14c0
def M0p7b15c0 : List Entry := [((0,0),[M0w39,M0w55,M0w66,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b15c0Ok : M0p7b15c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b15 : List Entry := M0p7b15c0
def M0p7b16c0 : List Entry := [((0,0),[M0w39,M0w46,M0w70,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w70,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w75,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w81,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w82,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w89,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w128,M0w155,M0w188]),
((0,0),[M0w39,M0w70,M0w121,M0w155,M0w188,M0w207])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b16c0Ok : M0p7b16c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b16 : List Entry := M0p7b16c0
def M0p7b17c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w107,M0w121,M0w155,M0w188,M0w205]),
((0,0),[M0w39,M0w55,M0w97,M0w117,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w132,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b17c0Ok : M0p7b17c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b17 : List Entry := M0p7b17c0
def M0p7b18c0 : List Entry := [((0,0),[M0w9,M0w17,M0w39,M0w55,M0w97,M0w121,M0w155]),
((0,0),[M0w17,M0w39,M0w55,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w73,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w112,M0w155,M0w188]),
((0,0),[M0w55,M0w97,M0w108,M0w121,M0w146,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b18c0Ok : M0p7b18c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b18 : List Entry := M0p7b18c0
def M0p7b19c0 : List Entry := [((0,0),[M0w35,M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b19c0Ok : M0p7b19c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b19 : List Entry := M0p7b19c0
def M0p7b20c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w120,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b20c0Ok : M0p7b20c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b20 : List Entry := M0p7b20c0
def M0p7b21c0 : List Entry := [((0,0),[M0w9,M0w39,M0w46,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w9,M0w39,M0w55,M0w97,M0w121,M0w144,M0w155]),
((0,0),[M0w9,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w9,M0w39,M0w55,M0w97,M0w130,M0w155,M0w188]),
((0,0),[M0w9,M0w39,M0w97,M0w121,M0w155,M0w188,M0w207]),
((0,0),[M0w9,M0w39,M0w97,M0w121,M0w155,M0w207]),
((0,0),[M0w10,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w55,M0w121,M0w133,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c0Ok : M0p7b21c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b21c1 : List Entry := [((0,0),[M0w39,M0w40,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w41,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w57,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w80,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w88,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w119,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w133,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c1Ok : M0p7b21c1.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b21c2 : List Entry := [((0,0),[M0w39,M0w55,M0w121,M0w133,M0w188,M0w198]),
((0,0),[M0w39,M0w55,M0w121,M0w136,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w155,M0w177,M0w188]),
((0,0),[M0w39,M0w121,M0w133,M0w155,M0w188,M0w207])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b21c2Ok : M0p7b21c2.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b21 : List Entry := M0p7b21c0 ++ M0p7b21c1 ++ M0p7b21c2
def M0p7b22c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w97,M0w108,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w114,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w137,M0w155,M0w188,M0w205]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w142,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b22c0Ok : M0p7b22c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b22 : List Entry := M0p7b22c0
def M0p7b23c0 : List Entry := [((0,0),[M0w0,M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w9,M0w39,M0w55,M0w68,M0w97,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w55,M0w68,M0w97,M0w121,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w176,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w183,M0w188]),
((0,0),[M0w39,M0w77,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b23c0Ok : M0p7b23c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b23 : List Entry := M0p7b23c0
def M0p7b25c0 : List Entry := [((0,0),[M0w3,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w9,M0w39,M0w55,M0w97,M0w108,M0w155,M0w188]),
((0,0),[M0w35,M0w55,M0w97,M0w108,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w97,M0w108,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w86,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w108,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w108,M0w155,M0w188,M0w196]),
((0,0),[M0w39,M0w55,M0w97,M0w109,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b25c0Ok : M0p7b25c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b25c1 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w111,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w189]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w190]),
((0,0),[M0w39,M0w55,M0w121,M0w135,M0w155,M0w188]),
((0,0),[M0w39,M0w97,M0w108,M0w121,M0w155,M0w188,M0w207]),
((0,0),[M0w55,M0w97,M0w108,M0w121,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b25c1Ok : M0p7b25c1.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b25 : List Entry := M0p7b25c0 ++ M0p7b25c1
def M0p7b26c0 : List Entry := [((0,0),[M0w9,M0w39,M0w55,M0w97,M0w137,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w91,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w153,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w197]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w157,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b26c0Ok : M0p7b26c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b26 : List Entry := M0p7b26c0
def M0p7b27c0 : List Entry := [((0,0),[M0w9,M0w39,M0w55,M0w70,M0w121,M0w155,M0w188]),
((0,0),[M0w11,M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w55,M0w97,M0w121,M0w159,M0w188]),
((0,0),[M0w39,M0w42,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w43,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w68,M0w97,M0w108,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w138,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w121,M0w143,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b27c0Ok : M0p7b27c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b27 : List Entry := M0p7b27c0
def M0p7b28c0 : List Entry := [((0,0),[M0w39,M0w55,M0w93,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b28c0Ok : M0p7b28c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b28 : List Entry := M0p7b28c0
def M0p7b29c0 : List Entry := [((0,0),[M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w188,M0w202])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b29c0Ok : M0p7b29c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b29 : List Entry := M0p7b29c0
def M0p7b30c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w108,M0w137,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w199]),
((0,0),[M0w39,M0w60,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b30c0Ok : M0p7b30c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b30 : List Entry := M0p7b30c0
def M0p7b31c0 : List Entry := [((0,0),[M0w6,M0w55,M0w97,M0w121,M0w146,M0w155,M0w188]),
((0,0),[M0w17,M0w39,M0w55,M0w97,M0w121,M0w146,M0w188]),
((0,0),[M0w35,M0w55,M0w97,M0w121,M0w146,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w97,M0w121,M0w146,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w70,M0w108,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w146,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w146,M0w188,M0w198]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w147,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c0Ok : M0p7b31c0.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b31c1 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w148,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w150,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w152,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w191]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w192]),
((0,0),[M0w39,M0w55,M0w120,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w97,M0w121,M0w146,M0w155,M0w188,M0w207]),
((0,0),[M0w55,M0w97,M0w110,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c1Ok : M0p7b31c1.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b31c2 : List Entry := [((0,0),[M0w55,M0w97,M0w121,M0w146,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p7b31c2Ok : M0p7b31c2.all (testRow chart64 none M0t6 6) = true := by decide +kernel

def M0p7b31 : List Entry := M0p7b31c0 ++ M0p7b31c1 ++ M0p7b31c2
def M0g7 : List (List Entry) := [M0p7b0, M0p7b1, M0p7b2, M0p7b3, M0p7b4, M0p7b5, M0p7b6, M0p7b7, M0p7b8, M0p7b9, M0p7b10, M0p7b11, [], M0p7b13, M0p7b14, M0p7b15, M0p7b16, M0p7b17, M0p7b18, M0p7b19, M0p7b20, M0p7b21, M0p7b22, M0p7b23, [], M0p7b25, M0p7b26, M0p7b27, M0p7b28, M0p7b29, M0p7b30, M0p7b31]
def M0t7 : Nat → List Entry := bucketOf M0g7
lemma M0v7 : verifiedR none 9 7 M0t7 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v6
  apply checkBuckets
  simp only [M0g7, M0p7b0, M0p7b1, M0p7b2, M0p7b3, M0p7b4, M0p7b5, M0p7b6, M0p7b7, M0p7b8, M0p7b9, M0p7b10, M0p7b11, M0p7b13, M0p7b14, M0p7b15, M0p7b16, M0p7b17, M0p7b18, M0p7b19, M0p7b20, M0p7b21, M0p7b22, M0p7b23, M0p7b25, M0p7b26, M0p7b27, M0p7b28, M0p7b29, M0p7b30, M0p7b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p7b0c0Ok, M0p7b1c0Ok, M0p7b2c0Ok, M0p7b3c0Ok, M0p7b4c0Ok, M0p7b5c0Ok, M0p7b6c0Ok, M0p7b7c0Ok, M0p7b7c1Ok, M0p7b7c2Ok, M0p7b8c0Ok, M0p7b9c0Ok, M0p7b10c0Ok, M0p7b10c1Ok, M0p7b10c2Ok, M0p7b10c3Ok, M0p7b10c4Ok, M0p7b10c5Ok, M0p7b10c6Ok, M0p7b10c7Ok, M0p7b10c8Ok, M0p7b10c9Ok, M0p7b10c10Ok, M0p7b11c0Ok, M0p7b13c0Ok, M0p7b14c0Ok, M0p7b15c0Ok, M0p7b16c0Ok, M0p7b17c0Ok, M0p7b18c0Ok, M0p7b19c0Ok, M0p7b20c0Ok, M0p7b21c0Ok, M0p7b21c1Ok, M0p7b21c2Ok, M0p7b22c0Ok, M0p7b23c0Ok, M0p7b25c0Ok, M0p7b25c1Ok, M0p7b26c0Ok, M0p7b27c0Ok, M0p7b28c0Ok, M0p7b29c0Ok, M0p7b30c0Ok, M0p7b31c0Ok, M0p7b31c1Ok, M0p7b31c2Ok]

def M0p8b1c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w163,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b1c0Ok : M0p8b1c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b1 : List Entry := M0p8b1c0
def M0p8b2c0 : List Entry := [((0,0),[M0w26,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b2c0Ok : M0p8b2c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b2 : List Entry := M0p8b2c0
def M0p8b4c0 : List Entry := [((0,0),[M0w39,M0w55,M0w78,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b4c0Ok : M0p8b4c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b4 : List Entry := M0p8b4c0
def M0p8b5c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w167,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b5c0Ok : M0p8b5c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b5 : List Entry := M0p8b5c0
def M0p8b6c0 : List Entry := [((0,0),[M0w2,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w6,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w35,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w62,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w205])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b6c0Ok : M0p8b6c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b6 : List Entry := M0p8b6c0
def M0p8b7c0 : List Entry := [((0,0),[M0w17,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w145,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w161,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w198])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b7c0Ok : M0p8b7c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b7 : List Entry := M0p8b7c0
def M0p8b8c0 : List Entry := [((0,0),[M0w39,M0w55,M0w79,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b8c0Ok : M0p8b8c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b8 : List Entry := M0p8b8c0
def M0p8b10c0 : List Entry := [((0,0),[M0w0,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w1,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w5,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w8,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w12,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w16,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w24,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w27,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c0Ok : M0p8b10c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b10c1 : List Entry := [((0,0),[M0w30,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w31,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w34,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w46,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w83,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w106,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w144,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c1Ok : M0p8b10c1.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b10c2 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w168,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w173,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w176,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w182,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w183,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w207]),
((0,0),[M0w39,M0w97,M0w121,M0w155,M0w188,M0w207])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b10c2Ok : M0p8b10c2.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b10 : List Entry := M0p8b10c0 ++ M0p8b10c1 ++ M0p8b10c2
def M0p8b12c0 : List Entry := [((0,0),[M0w25,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b12c0Ok : M0p8b12c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b12 : List Entry := M0p8b12c0
def M0p8b14c0 : List Entry := [((0,0),[M0w11,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w86,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b14c0Ok : M0p8b14c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b14 : List Entry := M0p8b14c0
def M0p8b16c0 : List Entry := [((0,0),[M0w28,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w70,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w84,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w105,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w202])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b16c0Ok : M0p8b16c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b16 : List Entry := M0p8b16c0
def M0p8b17c0 : List Entry := [((0,0),[M0w39,M0w55,M0w63,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b17c0Ok : M0p8b17c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b17 : List Entry := M0p8b17c0
def M0p8b18c0 : List Entry := [((0,0),[M0w14,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b18c0Ok : M0p8b18c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b18 : List Entry := M0p8b18c0
def M0p8b20c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w103,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b20c0Ok : M0p8b20c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b20 : List Entry := M0p8b20c0
def M0p8b21c0 : List Entry := [((0,0),[M0w9,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w107,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w130,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w132,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188,M0w196]),
((0,0),[M0w39,M0w55,M0w121,M0w133,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b21c0Ok : M0p8b21c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b21 : List Entry := M0p8b21c0
def M0p8b22c0 : List Entry := [((0,0),[M0w39,M0w55,M0w70,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b22c0Ok : M0p8b22c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b22 : List Entry := M0p8b22c0
def M0p8b23c0 : List Entry := [((0,0),[M0w39,M0w55,M0w68,M0w97,M0w121,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w129,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b23c0Ok : M0p8b23c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b23 : List Entry := M0p8b23c0
def M0p8b24c0 : List Entry := [((0,0),[M0w39,M0w55,M0w85,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b24c0Ok : M0p8b24c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b24 : List Entry := M0p8b24c0
def M0p8b25c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w108,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b25c0Ok : M0p8b25c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b25 : List Entry := M0p8b25c0
def M0p8b26c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w137,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b26c0Ok : M0p8b26c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b26 : List Entry := M0p8b26c0
def M0p8b27c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w133,M0w155,M0w188]),
((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w159,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b27c0Ok : M0p8b27c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b27 : List Entry := M0p8b27c0
def M0p8b30c0 : List Entry := [((0,0),[M0w23,M0w39,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b30c0Ok : M0p8b30c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b30 : List Entry := M0p8b30c0
def M0p8b31c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w146,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p8b31c0Ok : M0p8b31c0.all (testRow chart64 none M0t7 7) = true := by decide +kernel

def M0p8b31 : List Entry := M0p8b31c0
def M0g8 : List (List Entry) := [[], M0p8b1, M0p8b2, [], M0p8b4, M0p8b5, M0p8b6, M0p8b7, M0p8b8, [], M0p8b10, [], M0p8b12, [], M0p8b14, [], M0p8b16, M0p8b17, M0p8b18, [], M0p8b20, M0p8b21, M0p8b22, M0p8b23, M0p8b24, M0p8b25, M0p8b26, M0p8b27, [], [], M0p8b30, M0p8b31]
def M0t8 : Nat → List Entry := bucketOf M0g8
lemma M0v8 : verifiedR none 9 8 M0t8 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v7
  apply checkBuckets
  simp only [M0g8, M0p8b1, M0p8b2, M0p8b4, M0p8b5, M0p8b6, M0p8b7, M0p8b8, M0p8b10, M0p8b12, M0p8b14, M0p8b16, M0p8b17, M0p8b18, M0p8b20, M0p8b21, M0p8b22, M0p8b23, M0p8b24, M0p8b25, M0p8b26, M0p8b27, M0p8b30, M0p8b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p8b1c0Ok, M0p8b2c0Ok, M0p8b4c0Ok, M0p8b5c0Ok, M0p8b6c0Ok, M0p8b7c0Ok, M0p8b8c0Ok, M0p8b10c0Ok, M0p8b10c1Ok, M0p8b10c2Ok, M0p8b12c0Ok, M0p8b14c0Ok, M0p8b16c0Ok, M0p8b17c0Ok, M0p8b18c0Ok, M0p8b20c0Ok, M0p8b21c0Ok, M0p8b22c0Ok, M0p8b23c0Ok, M0p8b24c0Ok, M0p8b25c0Ok, M0p8b26c0Ok, M0p8b27c0Ok, M0p8b30c0Ok, M0p8b31c0Ok]

def M0p9b10c0 : List Entry := [((0,0),[M0w39,M0w55,M0w97,M0w121,M0w155,M0w188])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0p9b10c0Ok : M0p9b10c0.all (testRow chart64 none M0t8 8) = true := by decide +kernel

def M0p9b10 : List Entry := M0p9b10c0
def M0g9 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], M0p9b10, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M0t9 : Nat → List Entry := bucketOf M0g9
lemma M0v9 : verifiedR none 9 9 M0t9 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M0v8
  apply checkBuckets
  simp only [M0g9, M0p9b10, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M0p9b10c0Ok]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M0Img : (fullRaw.toFinset.image restriction0.hom.fn).image can ⊆ insert zero M0Raw.toFinset := by decide +kernel

lemma M0LB {q} (h : Projection8403.Can q (fullRaw.toFinset.image restriction0.hom.fn)) : 10 ≤ q := by
  apply noCan M0Img M0Need ?_ h
  intro k lim live
  have eq := sortFinset M0Raw
  exact M0v9 (0,0) (sortSignals M0Raw) (hit_mem (by decide +kernel))
    (by decide +kernel) (by simp [preserve,resources]) k lim (eq.symm ▸ live)

def M5Raw : List Sig := [(0x4a952455555554a952455555554a9524,0x75f75f75f75f75f75f75f75f75f75f75), (0xd9b36ecccccccd9b36ecccccccd9b36e,0x2c02c02c02c02c02c02c02c02c02c02c), (0xe1c38c0f0f0f0e1c38c0f0f0f0e1c38c,0xcfecfecfecfecfecfecfecfecfecfecf), (0x1fc07cff00ff01fc07cff00ff01fc07c,0xc05c05c05c05c05c05c05c05c05c05c0), (0x1fff80ffff0001fff80ffff0001fff80,0x600600600600600600600600600600), (0xe00000fffffffe00000fffffffe00000,0x800800800800800800800800800800)]

lemma M5Need : necessary M5Raw := needFrom (pn := [(0,4), (2,6), (0,1), (2,2), (7,1), (21,1)]) (by decide) (by decide +kernel)

def M5w0 : Sig := (0x1110000000000111000000,0x51951951951951951951951951951951)
def M5w1 : Sig := (0x1010100000000101010000000,0x41e41e41e41e41e41e41e41e41e41e41)
def M5w2 : Sig := (0xf0f0f0f000000f0f0f0f000000,0x0)
def M5w3 : Sig := (0xffff000000000ffff000000000,0x0)
def M5w4 : Sig := (0x7c0000ff000007c0000ff000007c,0xc01c01c01c01c01c01c01c01c01c01c0)
def M5w5 : Sig := (0x3f8000ff000003f8000ff000003f80,0x200200200200200200200200200200)
def M5w6 : Sig := (0x408000000000040800000000004080,0xc36c36c36c36c36c36c36c36c36c36c3)
def M5w7 : Sig := (0x1c3800f0f00001c3800f0f00001c380,0x600600600600600600600600600600)
def M5w8 : Sig := (0x1c38c000000001c38c000000001c38c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w9 : Sig := (0x1c38c0f000f001c38c0f000f001c38c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w10 : Sig := (0x1c38c0f0f00001c38c0f0f00001c38c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w11 : Sig := (0x2040000000000204000000000020400,0x51751751751751751751751751751751)
def M5w12 : Sig := (0x2040011111110204001111111020400,0x51f51f51f51f51f51f51f51f51f51f51)
def M5w13 : Sig := (0x6441033113310644103311331064410,0xd1fd1fd1fd1fd1fd1fd1fd1fd1fd1fd1)
def M5w14 : Sig := (0x64c803333000064c803333000064c80,0x600600600600600600600600600600)
def M5w15 : Sig := (0xa142050505050a142050505050a1420,0x30130130130130130130130130130130)
def M5w16 : Sig := (0xa950055550000a950055550000a9500,0x600600600600600600600600600600)
def M5w17 : Sig := (0xa952400000000a952400000000a9524,0x75775775775775775775775775775775)
def M5w18 : Sig := (0xa952450505050a952450505050a9524,0x75775775775775775775775775775775)
def M5w19 : Sig := (0xa952455005500a952455005500a9524,0x75775775775775775775775775775775)
def M5w20 : Sig := (0xa952455550000a952455550000a9524,0x75775775775775775775775775775775)
def M5w21 : Sig := (0xbd7ac00000000bd7ac00000000bd7ac,0xff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff)
def M5w22 : Sig := (0x156a80aaaa000156a80aaaa000156a80,0x0)
def M5w23 : Sig := (0x19f3ee000000019f3ee000000019f3ee,0xef6ef6ef6ef6ef6ef6ef6ef6ef6ef6ef)
def M5w24 : Sig := (0x1bb76e00000001bb76e00000001bb76e,0x7d77d77d77d77d77d77d77d77d77d77d)
def M5w25 : Sig := (0x1e3c00f0f00001e3c00f0f00001e3c00,0x0)
def M5w26 : Sig := (0x1fc07cff00ff01fc07cff00ff01fc07c,0xc05c05c05c05c05c05c05c05c05c05c0)
def M5w27 : Sig := (0x1fc07cfff0fff1fc07cfff0fff1fc07c,0xc05c05c05c05c05c05c05c05c05c05c0)
def M5w28 : Sig := (0x1fc07cffffff01fc07cffffff01fc07c,0xc05c05c05c05c05c05c05c05c05c05c0)
def M5w29 : Sig := (0x1fc3fcff0fff01fc3fcff0fff01fc3fc,0xc07c07c07c07c07c07c07c07c07c07c0)
def M5w30 : Sig := (0x1fccfcff33ff01fccfcff33ff01fccfc,0xc07c07c07c07c07c07c07c07c07c07c0)
def M5w31 : Sig := (0x1fd57cff55ff01fd57cff55ff01fd57c,0xc07c07c07c07c07c07c07c07c07c07c0)
def M5w32 : Sig := (0x1fff8000000001fff8000000001fff80,0x600600600600600600600600600600)
def M5w33 : Sig := (0x1fff80ffff0001fff80ffff0001fff80,0x600600600600600600600600600600)
def M5w34 : Sig := (0x1fff80fffff0f1fff80fffff0f1fff80,0x600600600600600600600600600600)
def M5w35 : Sig := (0x1fff8c00000001fff8c00000001fff8c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w36 : Sig := (0x1fff8cffff0001fff8cffff0001fff8c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w37 : Sig := (0x1fffa400000001fffa400000001fffa4,0x75775775775775775775775775775775)
def M5w38 : Sig := (0x1fffa4ffff0001fffa4ffff0001fffa4,0x75775775775775775775775775775775)
def M5w39 : Sig := (0x1ffffcff00ff01ffffcff00ff01ffffc,0xc07c07c07c07c07c07c07c07c07c07c0)
def M5w40 : Sig := (0x1ffffcffffff01ffffcffffff01ffffc,0xc07c07c07c07c07c07c07c07c07c07c0)
def M5w41 : Sig := (0x20000000000302000000000030200000,0xc38c38c38c38c38c38c38c38c38c38c3)
def M5w42 : Sig := (0x20000033333332000003333333200000,0x800800800800800800800800800800)
def M5w43 : Sig := (0x20408003030302040800303030204080,0xc3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3)
def M5w44 : Sig := (0x26409033033302640903303330264090,0xc3fc3fc3fc3fc3fc3fc3fc3fc3fc3fc3)
def M5w45 : Sig := (0x264c803333333264c803333333264c80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w46 : Sig := (0x3fff80ffff3333fff80ffff3333fff80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w47 : Sig := (0x40000055555554000005555555400000,0x800800800800800800800800800800)
def M5w48 : Sig := (0x40002400005554000240000555400024,0x75975975975975975975975975975975)
def M5w49 : Sig := (0x40150000550054015000055005401500,0x35a35a35a35a35a35a35a35a35a35a35)
def M5w50 : Sig := (0x40810405050504081040505050408104,0x45e45e45e45e45e45e45e45e45e45e45)
def M5w51 : Sig := (0x40812405055554081240505555408124,0x75f75f75f75f75f75f75f75f75f75f75)
def M5w52 : Sig := (0x41c38c050505041c38c050505041c38c,0xcfecfecfecfecfecfecfecfecfecfecf)
def M5w53 : Sig := (0x4a142055555554a142055555554a1420,0x30930930930930930930930930930930)
def M5w54 : Sig := (0x4a950055555554a950055555554a9500,0xe00e00e00e00e00e00e00e00e00e00)
def M5w55 : Sig := (0x4a952400005554a952400005554a9524,0x75f75f75f75f75f75f75f75f75f75f75)
def M5w56 : Sig := (0x4a952405050504a952405050504a9524,0x75f75f75f75f75f75f75f75f75f75f75)
def M5w57 : Sig := (0x4a952444444444a952444444444a9524,0x75775775775775775775775775775775)
def M5w58 : Sig := (0x4a952455555554a952455555554a9524,0x75f75f75f75f75f75f75f75f75f75f75)
def M5w59 : Sig := (0x5fd57cff55ff55fd57cff55ff55fd57c,0xf5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5)
def M5w60 : Sig := (0x5fff80ffff5555fff80ffff5555fff80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w61 : Sig := (0x5fffa4ffff5555fffa4ffff5555fffa4,0x75f75f75f75f75f75f75f75f75f75f75)
def M5w62 : Sig := (0xa00000aaaaaaaa00000aaaaaaaa00000,0x0)
def M5w63 : Sig := (0xa142880a0a0a0a142880a0a0a0a14288,0x8a08a08a08a08a08a08a08a08a08a08a)
def M5w64 : Sig := (0xa1c38c0a0a0a0a1c38c0a0a0a0a1c38c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w65 : Sig := (0xbfc07cffaaffabfc07cffaaffabfc07c,0xc05c05c05c05c05c05c05c05c05c05c0)
def M5w66 : Sig := (0xbfff80ffffaaabfff80ffffaaabfff80,0x600600600600600600600600600600)
def M5w67 : Sig := (0xc0370200dd00dc0370200dd00dc03702,0x3da3da3da3da3da3da3da3da3da3da3d)
def M5w68 : Sig := (0xc1c38c0c0c0c0c1c38c0c0c0c0c1c38c,0xcf6cf6cf6cf6cf6cf6cf6cf6cf6cf6cf)
def M5w69 : Sig := (0xd9b36ecccccccd9b36ecccccccd9b36e,0x2c02c02c02c02c02c02c02c02c02c02c)
def M5w70 : Sig := (0xd9b36efcfcfcfd9b36efcfcfcfd9b36e,0x2c02c02c02c02c02c02c02c02c02c02c)
def M5w71 : Sig := (0xd9b36effffcccd9b36effffcccd9b36e,0x2c02c02c02c02c02c02c02c02c02c02c)
def M5w72 : Sig := (0xd9f3eecccccccd9f3eecccccccd9f3ee,0xef6ef6ef6ef6ef6ef6ef6ef6ef6ef6ef)
def M5w73 : Sig := (0xdbb76ecccccccdbb76ecccccccdbb76e,0x7d77d77d77d77d77d77d77d77d77d77d)
def M5w74 : Sig := (0xdbb76eddddddddbb76eddddddddbb76e,0x7df7df7df7df7df7df7df7df7df7df7d)
def M5w75 : Sig := (0xddfbeeeeeecccddfbeeeeeecccddfbee,0x2c02c02c02c02c02c02c02c02c02c02c)
def M5w76 : Sig := (0xdfbf6efcfccccdfbf6efcfccccdfbf6e,0x2c02c02c02c02c02c02c02c02c02c02c)
def M5w77 : Sig := (0xdfffeeffffcccdfffeeffffcccdfffee,0x2c62c62c62c62c62c62c62c62c62c62c)
def M5w78 : Sig := (0xe000000000fffe000000000fffe00000,0x800800800800800800800800800800)
def M5w79 : Sig := (0xe0000000ff00fe0000000ff00fe00000,0x800800800800800800800800800800)
def M5w80 : Sig := (0xe000000f0f0f0e000000f0f0f0e00000,0x800800800800800800800800800800)
def M5w81 : Sig := (0xe00000fffffffe00000fffffffe00000,0x800800800800800800800800800800)
def M5w82 : Sig := (0xe0000c00000f0e0000c00000f0e0000c,0xcf8cf8cf8cf8cf8cf8cf8cf8cf8cf8cf)
def M5w83 : Sig := (0xe0002c00005f5e0002c00005f5e0002c,0xff9ff9ff9ff9ff9ff9ff9ff9ff9ff9ff)
def M5w84 : Sig := (0xe00380000f000e00380000f000e00380,0xfa0fa0fa0fa0fa0fa0fa0fa0fa0fa0f)
def M5w85 : Sig := (0xe0330200ff00fe0330200ff00fe03302,0x2c82c82c82c82c82c82c82c82c82c82c)
def M5w86 : Sig := (0xe0338200cf00ce0338200cf00ce03382,0x2fa2fa2fa2fa2fa2fa2fa2fa2fa2fa2f)
def M5w87 : Sig := (0xe0810c05050f0e0810c05050f0e0810c,0xcfecfecfecfecfecfecfecfecfecfecf)
def M5w88 : Sig := (0xe142880f0f0f0e142880f0f0f0e14288,0x8a88a88a88a88a88a88a88a88a88a88a)
def M5w89 : Sig := (0xe14288fffffffe14288fffffffe14288,0x8a88a88a88a88a88a88a88a88a88a88a)
def M5w90 : Sig := (0xe1c3800f0f0f0e1c3800f0f0f0e1c380,0xe00e00e00e00e00e00e00e00e00e00)
def M5w91 : Sig := (0xe1c380fffffffe1c380fffffffe1c380,0xe00e00e00e00e00e00e00e00e00e00)
def M5w92 : Sig := (0xe1c38c00000f0e1c38c00000f0e1c38c,0xcfecfecfecfecfecfecfecfecfecfecf)
def M5w93 : Sig := (0xe1c38c0f0f0f0e1c38c0f0f0f0e1c38c,0xcfecfecfecfecfecfecfecfecfecfecf)
def M5w94 : Sig := (0xe1c38cfffffffe1c38cfffffffe1c38c,0xcfecfecfecfecfecfecfecfecfecfecf)
def M5w95 : Sig := (0xe64c80fffffffe64c80fffffffe64c80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w96 : Sig := (0xea1420fffffffea1420fffffffea1420,0x30930930930930930930930930930930)
def M5w97 : Sig := (0xea9500fffffffea9500fffffffea9500,0xe00e00e00e00e00e00e00e00e00e00)
def M5w98 : Sig := (0xea9524fffffffea9524fffffffea9524,0x75f75f75f75f75f75f75f75f75f75f75)
def M5w99 : Sig := (0xebd7ac5f5f5f5ebd7ac5f5f5f5ebd7ac,0xffffffffffffffffffffffffffffffff)
def M5w100 : Sig := (0xf56a80ffffffff56a80ffffffff56a80,0x800800800800800800800800800800)
def M5w101 : Sig := (0xf9b36eeeeeeeef9b36eeeeeeeef9b36e,0x2c02c02c02c02c02c02c02c02c02c02c)
def M5w102 : Sig := (0xf9b36effffffff9b36effffffff9b36e,0x2c82c82c82c82c82c82c82c82c82c82c)
def M5w103 : Sig := (0xf9f3eecfcfcfcf9f3eecfcfcfcf9f3ee,0xefeefeefeefeefeefeefeefeefeefeef)
def M5w104 : Sig := (0xfe3c00ffffffffe3c00ffffffffe3c00,0x800800800800800800800800800800)
def M5w105 : Sig := (0xffc07cfffffffffc07cfffffffffc07c,0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0)
def M5w106 : Sig := (0xffc3fcff0fff0ffc3fcff0fff0ffc3fc,0xcffcffcffcffcffcffcffcffcffcffcf)
def M5w107 : Sig := (0xffff80ffff00fffff80ffff00fffff80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w108 : Sig := (0xffff80ffff0f0ffff80ffff0f0ffff80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w109 : Sig := (0xffff80fffffffffff80fffffffffff80,0xe00e00e00e00e00e00e00e00e00e00)
def M5w110 : Sig := (0xffff8cffff0f0ffff8cffff0f0ffff8c,0xcfecfecfecfecfecfecfecfecfecfecf)
def M5t0 : Nat → List Entry := fun _ => []

lemma M5v0 : verifiedR none 9 0 M5t0 := emptyR _ _

def M5g1 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M5t1 : Nat → List Entry := bucketOf M5g1
lemma M5v1 : verifiedR none 9 1 M5t1 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v0
  apply checkBuckets
  simp only [M5g1, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M5g2 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M5t2 : Nat → List Entry := bucketOf M5g2
lemma M5v2 : verifiedR none 9 2 M5t2 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v1
  apply checkBuckets
  simp only [M5g2, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M5g3 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M5t3 : Nat → List Entry := bucketOf M5g3
lemma M5v3 : verifiedR none 9 3 M5t3 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v2
  apply checkBuckets
  simp only [M5g3, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M5g4 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M5t4 : Nat → List Entry := bucketOf M5g4
lemma M5v4 : verifiedR none 9 4 M5t4 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v3
  apply checkBuckets
  simp only [M5g4, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def M5p5b3c0 : List Entry := [((0,0),[M5w26,M5w48,M5w57,M5w69,M5w93,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p5b3c0Ok : M5p5b3c0.all (testRow chart64 none M5t4 4) = true := by decide +kernel

def M5p5b3 : List Entry := M5p5b3c0
def M5p5b5c0 : List Entry := [((0,0),[M5w26,M5w58,M5w68,M5w69,M5w82,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p5b5c0Ok : M5p5b5c0.all (testRow chart64 none M5t4 4) = true := by decide +kernel

def M5p5b5 : List Entry := M5p5b5c0
def M5p5b11c0 : List Entry := [((0,0),[M5w1,M5w8,M5w17,M5w26,M5w33,M5w69])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p5b11c0Ok : M5p5b11c0.all (testRow chart64 none M5t4 4) = true := by decide +kernel

def M5p5b11 : List Entry := M5p5b11c0
def M5g5 : List (List Entry) := [[], [], [], M5p5b3, [], M5p5b5, [], [], [], [], [], M5p5b11, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M5t5 : Nat → List Entry := bucketOf M5g5
lemma M5v5 : verifiedR none 9 5 M5t5 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v4
  apply checkBuckets
  simp only [M5g5, M5p5b3, M5p5b5, M5p5b11, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M5p5b3c0Ok, M5p5b5c0Ok, M5p5b11c0Ok]

def M5p6b3c0 : List Entry := [((0,0),[M5w17,M5w26,M5w48,M5w69,M5w93,M5w109]),
((0,0),[M5w17,M5w40,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w19,M5w26,M5w33,M5w48,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w48,M5w57,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w57,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w26,M5w42,M5w48,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w26,M5w46,M5w48,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w48,M5w58,M5w69,M5w81,M5w93,M5w107])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b3c0Ok : M5p6b3c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b3 : List Entry := M5p6b3c0
def M5p6b4c0 : List Entry := [((0,0),[M5w26,M5w58,M5w77,M5w93,M5w102,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b4c0Ok : M5p6b4c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b4 : List Entry := M5p6b4c0
def M5p6b5c0 : List Entry := [((0,0),[M5w8,M5w26,M5w58,M5w69,M5w82,M5w109]),
((0,0),[M5w8,M5w40,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w9,M5w26,M5w33,M5w58,M5w69,M5w81,M5w82]),
((0,0),[M5w26,M5w33,M5w58,M5w68,M5w69,M5w81,M5w82]),
((0,0),[M5w26,M5w33,M5w58,M5w68,M5w69,M5w93,M5w109]),
((0,0),[M5w26,M5w42,M5w58,M5w69,M5w82,M5w93,M5w109]),
((0,0),[M5w26,M5w46,M5w58,M5w69,M5w81,M5w82,M5w93]),
((0,0),[M5w26,M5w58,M5w69,M5w81,M5w82,M5w93,M5w107])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b5c0Ok : M5p6b5c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b5 : List Entry := M5p6b5c0
def M5p6b6c0 : List Entry := [((0,0),[M5w8,M5w17,M5w26,M5w33,M5w43,M5w58,M5w69])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b6c0Ok : M5p6b6c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b6 : List Entry := M5p6b6c0
def M5p6b10c0 : List Entry := [((0,0),[M5w21,M5w26,M5w33,M5w50,M5w69]),
((0,0),[M5w21,M5w26,M5w33,M5w50,M5w69,M5w81]),
((0,0),[M5w26,M5w50,M5w69,M5w81,M5w83])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b10c0Ok : M5p6b10c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b10 : List Entry := M5p6b10c0
def M5p6b11c0 : List Entry := [((0,0),[M5w1,M5w8,M5w26,M5w33,M5w58,M5w69,M5w81]),
((0,0),[M5w1,M5w17,M5w26,M5w33,M5w69,M5w81,M5w93]),
((0,0),[M5w1,M5w26,M5w33,M5w58,M5w81,M5w93,M5w102])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b11c0Ok : M5p6b11c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b11 : List Entry := M5p6b11c0
def M5p6b13c0 : List Entry := [((0,0),[M5w8,M5w26,M5w33,M5w43,M5w58,M5w77,M5w81]),
((0,0),[M5w26,M5w33,M5w43,M5w58,M5w81,M5w82,M5w102]),
((0,0),[M5w26,M5w33,M5w43,M5w58,M5w93,M5w102,M5w109]),
((0,0),[M5w40,M5w43,M5w58,M5w77,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b13c0Ok : M5p6b13c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b13 : List Entry := M5p6b13c0
def M5p6b19c0 : List Entry := [((0,0),[M5w8,M5w17,M5w26,M5w33,M5w50,M5w69])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b19c0Ok : M5p6b19c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b19 : List Entry := M5p6b19c0
def M5p6b22c0 : List Entry := [((0,0),[M5w8,M5w12,M5w17,M5w26,M5w33,M5w69,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b22c0Ok : M5p6b22c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b22 : List Entry := M5p6b22c0
def M5p6b27c0 : List Entry := [((0,0),[M5w12,M5w17,M5w26,M5w33,M5w77,M5w81,M5w93]),
((0,0),[M5w12,M5w26,M5w33,M5w48,M5w81,M5w93,M5w102]),
((0,0),[M5w12,M5w26,M5w33,M5w58,M5w93,M5w102,M5w109]),
((0,0),[M5w12,M5w40,M5w58,M5w77,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b27c0Ok : M5p6b27c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b27 : List Entry := M5p6b27c0
def M5p6b29c0 : List Entry := [((0,0),[M5w17,M5w26,M5w58,M5w69,M5w77,M5w93,M5w109]),
((0,0),[M5w26,M5w48,M5w58,M5w69,M5w93,M5w102,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b29c0Ok : M5p6b29c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b29 : List Entry := M5p6b29c0
def M5p6b31c0 : List Entry := [((0,0),[M5w8,M5w26,M5w58,M5w69,M5w77,M5w93,M5w109]),
((0,0),[M5w26,M5w58,M5w69,M5w82,M5w93,M5w102,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p6b31c0Ok : M5p6b31c0.all (testRow chart64 none M5t5 5) = true := by decide +kernel

def M5p6b31 : List Entry := M5p6b31c0
def M5g6 : List (List Entry) := [[], [], [], M5p6b3, M5p6b4, M5p6b5, M5p6b6, [], [], [], M5p6b10, M5p6b11, [], M5p6b13, [], [], [], [], [], M5p6b19, [], [], M5p6b22, [], [], [], [], M5p6b27, [], M5p6b29, [], M5p6b31]
def M5t6 : Nat → List Entry := bucketOf M5g6
lemma M5v6 : verifiedR none 9 6 M5t6 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v5
  apply checkBuckets
  simp only [M5g6, M5p6b3, M5p6b4, M5p6b5, M5p6b6, M5p6b10, M5p6b11, M5p6b13, M5p6b19, M5p6b22, M5p6b27, M5p6b29, M5p6b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M5p6b3c0Ok, M5p6b4c0Ok, M5p6b5c0Ok, M5p6b6c0Ok, M5p6b10c0Ok, M5p6b11c0Ok, M5p6b13c0Ok, M5p6b19c0Ok, M5p6b22c0Ok, M5p6b27c0Ok, M5p6b29c0Ok, M5p6b31c0Ok]

def M5p7b1c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w82,M5w93,M5w105])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b1c0Ok : M5p7b1c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b1 : List Entry := M5p7b1c0
def M5p7b3c0 : List Entry := [((0,0),[M5w4,M5w17,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w17,M5w26,M5w33,M5w48,M5w69,M5w81,M5w93]),
((0,0),[M5w17,M5w26,M5w33,M5w58,M5w69,M5w78,M5w93]),
((0,0),[M5w17,M5w26,M5w33,M5w58,M5w69,M5w80,M5w93]),
((0,0),[M5w17,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w17,M5w26,M5w33,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w17,M5w26,M5w33,M5w61,M5w69,M5w81,M5w93]),
((0,0),[M5w17,M5w33,M5w40,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b3c0Ok : M5p7b3c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b3c1 : List Entry := [((0,0),[M5w18,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w19,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w20,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w37,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w38,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w42,M5w48,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w44,M5w58,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w48,M5w58,M5w69,M5w79,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b3c1Ok : M5p7b3c1.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b3c2 : List Entry := [((0,0),[M5w26,M5w33,M5w57,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w48,M5w58,M5w69,M5w81,M5w93,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b3c2Ok : M5p7b3c2.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b3 : List Entry := M5p7b3c0 ++ M5p7b3c1 ++ M5p7b3c2
def M5p7b4c0 : List Entry := [((0,0),[M5w12,M5w26,M5w33,M5w43,M5w58,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w93,M5w102,M5w109]),
((0,0),[M5w26,M5w33,M5w58,M5w77,M5w81,M5w93,M5w102]),
((0,0),[M5w26,M5w58,M5w69,M5w77,M5w81,M5w93,M5w109]),
((0,0),[M5w40,M5w58,M5w69,M5w77,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b4c0Ok : M5p7b4c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b4 : List Entry := M5p7b4c0
def M5p7b5c0 : List Entry := [((0,0),[M5w4,M5w8,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w8,M5w26,M5w33,M5w47,M5w58,M5w69,M5w93]),
((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w78,M5w93]),
((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w81,M5w82]),
((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w81,M5w110]),
((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w8,M5w33,M5w40,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b5c0Ok : M5p7b5c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b5c1 : List Entry := [((0,0),[M5w9,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w10,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w35,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w36,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w42,M5w58,M5w69,M5w81,M5w82,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w64,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w68,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w79,M5w81,M5w82,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b5c1Ok : M5p7b5c1.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b5c2 : List Entry := [((0,0),[M5w26,M5w58,M5w69,M5w81,M5w82,M5w93,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b5c2Ok : M5p7b5c2.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b5 : List Entry := M5p7b5c0 ++ M5p7b5c1 ++ M5p7b5c2
def M5p7b6c0 : List Entry := [((0,0),[M5w17,M5w26,M5w33,M5w43,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b6c0Ok : M5p7b6c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b6 : List Entry := M5p7b6c0
def M5p7b7c0 : List Entry := [((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w81,M5w103]),
((0,0),[M5w23,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w72,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b7c0Ok : M5p7b7c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b7 : List Entry := M5p7b7c0
def M5p7b10c0 : List Entry := [((0,0),[M5w4,M5w33,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w7,M5w26,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w14,M5w26,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w14,M5w40,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w16,M5w26,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w26,M5w33,M5w42,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w26,M5w33,M5w45,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w46,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b10c0Ok : M5p7b10c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b10c1 : List Entry := [((0,0),[M5w26,M5w33,M5w47,M5w58,M5w69,M5w93,M5w109]),
((0,0),[M5w26,M5w33,M5w50,M5w69,M5w81,M5w99]),
((0,0),[M5w26,M5w33,M5w51,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w52,M5w58,M5w69,M5w81]),
((0,0),[M5w26,M5w33,M5w54,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w55,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w56,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w60,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b10c1Ok : M5p7b10c1.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b10c2 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w80,M5w93,M5w109]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w87]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w90,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w91,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w92]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w95]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w97]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w100])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b10c2Ok : M5p7b10c2.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b10c3 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w104]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w107]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w108]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w93,M5w100]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w93,M5w104]),
((0,0),[M5w26,M5w33,M5w58,M5w70,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w71,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b10c3Ok : M5p7b10c3.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b10c4 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w75,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w76,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w81,M5w93,M5w101]),
((0,0),[M5w26,M5w34,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w58,M5w66,M5w69,M5w81,M5w93]),
((0,0),[M5w27,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w28,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w29,M5w33,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b10c4Ok : M5p7b10c4.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b10c5 : List Entry := [((0,0),[M5w30,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w31,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w32,M5w40,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w33,M5w39,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w33,M5w40,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w33,M5w40,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w33,M5w58,M5w65,M5w69,M5w81,M5w93]),
((0,0),[M5w40,M5w58,M5w69,M5w81,M5w93,M5w109])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b10c5Ok : M5p7b10c5.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b10 : List Entry := M5p7b10c0 ++ M5p7b10c1 ++ M5p7b10c2 ++ M5p7b10c3 ++ M5p7b10c4 ++ M5p7b10c5
def M5p7b11c0 : List Entry := [((0,0),[M5w1,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b11c0Ok : M5p7b11c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b11 : List Entry := M5p7b11c0
def M5p7b13c0 : List Entry := [((0,0),[M5w6,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w8,M5w26,M5w33,M5w43,M5w58,M5w69,M5w81]),
((0,0),[M5w26,M5w33,M5w41,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w43,M5w58,M5w69,M5w81,M5w82]),
((0,0),[M5w26,M5w33,M5w43,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w26,M5w33,M5w43,M5w58,M5w77,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w43,M5w58,M5w81,M5w93,M5w102]),
((0,0),[M5w26,M5w33,M5w50,M5w58,M5w69,M5w81,M5w93,M5w102])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b13c0Ok : M5p7b13c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b13c1 : List Entry := [((0,0),[M5w33,M5w40,M5w43,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w33,M5w58,M5w67,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b13c1Ok : M5p7b13c1.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b13 : List Entry := M5p7b13c0 ++ M5p7b13c1
def M5p7b17c0 : List Entry := [((0,0),[M5w13,M5w26,M5w33,M5w58,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b17c0Ok : M5p7b17c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b17 : List Entry := M5p7b17c0
def M5p7b19c0 : List Entry := [((0,0),[M5w8,M5w26,M5w33,M5w50,M5w58,M5w69,M5w81]),
((0,0),[M5w17,M5w26,M5w33,M5w50,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b19c0Ok : M5p7b19c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b19 : List Entry := M5p7b19c0
def M5p7b21c0 : List Entry := [((0,0),[M5w17,M5w26,M5w33,M5w69,M5w74,M5w81,M5w93]),
((0,0),[M5w21,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w21,M5w26,M5w33,M5w58,M5w69,M5w93]),
((0,0),[M5w24,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w73,M5w81,M5w93]),
((0,0),[M5w26,M5w58,M5w69,M5w81,M5w83,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b21c0Ok : M5p7b21c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b21 : List Entry := M5p7b21c0
def M5p7b22c0 : List Entry := [((0,0),[M5w8,M5w12,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b22c0Ok : M5p7b22c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b22 : List Entry := M5p7b22c0
def M5p7b26c0 : List Entry := [((0,0),[M5w8,M5w15,M5w26,M5w33,M5w58,M5w69,M5w81]),
((0,0),[M5w26,M5w33,M5w53,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w96])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b26c0Ok : M5p7b26c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b26 : List Entry := M5p7b26c0
def M5p7b27c0 : List Entry := [((0,0),[M5w0,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w11,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w12,M5w17,M5w26,M5w33,M5w69,M5w81,M5w93]),
((0,0),[M5w12,M5w26,M5w33,M5w48,M5w69,M5w81,M5w93]),
((0,0),[M5w12,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w12,M5w26,M5w33,M5w58,M5w77,M5w81,M5w93]),
((0,0),[M5w12,M5w26,M5w33,M5w58,M5w81,M5w93,M5w102]),
((0,0),[M5w12,M5w33,M5w40,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b27c0Ok : M5p7b27c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b27 : List Entry := M5p7b27c0
def M5p7b28c0 : List Entry := [((0,0),[M5w17,M5w26,M5w33,M5w63,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w88,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w89,M5w93]),
((0,0),[M5w33,M5w58,M5w69,M5w81,M5w85,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b28c0Ok : M5p7b28c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b28 : List Entry := M5p7b28c0
def M5p7b29c0 : List Entry := [((0,0),[M5w17,M5w26,M5w33,M5w58,M5w69,M5w77,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w48,M5w58,M5w69,M5w81,M5w93,M5w102])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b29c0Ok : M5p7b29c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b29 : List Entry := M5p7b29c0
def M5p7b30c0 : List Entry := [((0,0),[M5w8,M5w17,M5w26,M5w33,M5w58,M5w69,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b30c0Ok : M5p7b30c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b30 : List Entry := M5p7b30c0
def M5p7b31c0 : List Entry := [((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w77,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w48,M5w58,M5w69,M5w81,M5w93,M5w105]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w82,M5w93,M5w102]),
((0,0),[M5w33,M5w58,M5w69,M5w81,M5w86,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p7b31c0Ok : M5p7b31c0.all (testRow chart64 none M5t6 6) = true := by decide +kernel

def M5p7b31 : List Entry := M5p7b31c0
def M5g7 : List (List Entry) := [[], M5p7b1, [], M5p7b3, M5p7b4, M5p7b5, M5p7b6, M5p7b7, [], [], M5p7b10, M5p7b11, [], M5p7b13, [], [], [], M5p7b17, [], M5p7b19, [], M5p7b21, M5p7b22, [], [], [], M5p7b26, M5p7b27, M5p7b28, M5p7b29, M5p7b30, M5p7b31]
def M5t7 : Nat → List Entry := bucketOf M5g7
lemma M5v7 : verifiedR none 9 7 M5t7 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v6
  apply checkBuckets
  simp only [M5g7, M5p7b1, M5p7b3, M5p7b4, M5p7b5, M5p7b6, M5p7b7, M5p7b10, M5p7b11, M5p7b13, M5p7b17, M5p7b19, M5p7b21, M5p7b22, M5p7b26, M5p7b27, M5p7b28, M5p7b29, M5p7b30, M5p7b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M5p7b1c0Ok, M5p7b3c0Ok, M5p7b3c1Ok, M5p7b3c2Ok, M5p7b4c0Ok, M5p7b5c0Ok, M5p7b5c1Ok, M5p7b5c2Ok, M5p7b6c0Ok, M5p7b7c0Ok, M5p7b10c0Ok, M5p7b10c1Ok, M5p7b10c2Ok, M5p7b10c3Ok, M5p7b10c4Ok, M5p7b10c5Ok, M5p7b11c0Ok, M5p7b13c0Ok, M5p7b13c1Ok, M5p7b17c0Ok, M5p7b19c0Ok, M5p7b21c0Ok, M5p7b22c0Ok, M5p7b26c0Ok, M5p7b27c0Ok, M5p7b28c0Ok, M5p7b29c0Ok, M5p7b30c0Ok, M5p7b31c0Ok]

def M5p8b3c0 : List Entry := [((0,0),[M5w17,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w48,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w61,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w98])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b3c0Ok : M5p8b3c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b3 : List Entry := M5p8b3c0
def M5p8b4c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w77,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w102])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b4c0Ok : M5p8b4c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b4 : List Entry := M5p8b4c0
def M5p8b5c0 : List Entry := [((0,0),[M5w8,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w82,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w94]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w110])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b5c0Ok : M5p8b5c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b5 : List Entry := M5p8b5c0
def M5p8b6c0 : List Entry := [((0,0),[M5w26,M5w33,M5w40,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w105])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b6c0Ok : M5p8b6c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b6 : List Entry := M5p8b6c0
def M5p8b7c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w103])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b7c0Ok : M5p8b7c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b7 : List Entry := M5p8b7c0
def M5p8b10c0 : List Entry := [((0,0),[M5w2,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w3,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w4,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w5,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w7,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w14,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w16,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w22,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b10c0Ok : M5p8b10c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b10c1 : List Entry := [((0,0),[M5w25,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w32,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w42,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w47,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w62,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w78,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w79,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w80,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b10c1Ok : M5p8b10c1.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b10c2 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w109]),
((0,0),[M5w33,M5w40,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b10c2Ok : M5p8b10c2.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b10 : List Entry := M5p8b10c0 ++ M5p8b10c1 ++ M5p8b10c2
def M5p8b13c0 : List Entry := [((0,0),[M5w26,M5w33,M5w43,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b13c0Ok : M5p8b13c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b13 : List Entry := M5p8b13c0
def M5p8b19c0 : List Entry := [((0,0),[M5w26,M5w33,M5w50,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b19c0Ok : M5p8b19c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b19 : List Entry := M5p8b19c0
def M5p8b21c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w74,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w99]),
((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93,M5w106])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b21c0Ok : M5p8b21c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b21 : List Entry := M5p8b21c0
def M5p8b25c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w84,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b25c0Ok : M5p8b25c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b25 : List Entry := M5p8b25c0
def M5p8b26c0 : List Entry := [((0,0),[M5w15,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b26c0Ok : M5p8b26c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b26 : List Entry := M5p8b26c0
def M5p8b27c0 : List Entry := [((0,0),[M5w12,M5w26,M5w33,M5w58,M5w69,M5w81,M5w93]),
((0,0),[M5w26,M5w33,M5w58,M5w59,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b27c0Ok : M5p8b27c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b27 : List Entry := M5p8b27c0
def M5p8b28c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w63,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b28c0Ok : M5p8b28c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b28 : List Entry := M5p8b28c0
def M5p8b31c0 : List Entry := [((0,0),[M5w26,M5w33,M5w49,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p8b31c0Ok : M5p8b31c0.all (testRow chart64 none M5t7 7) = true := by decide +kernel

def M5p8b31 : List Entry := M5p8b31c0
def M5g8 : List (List Entry) := [[], [], [], M5p8b3, M5p8b4, M5p8b5, M5p8b6, M5p8b7, [], [], M5p8b10, [], [], M5p8b13, [], [], [], [], [], M5p8b19, [], M5p8b21, [], [], [], M5p8b25, M5p8b26, M5p8b27, M5p8b28, [], [], M5p8b31]
def M5t8 : Nat → List Entry := bucketOf M5g8
lemma M5v8 : verifiedR none 9 8 M5t8 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v7
  apply checkBuckets
  simp only [M5g8, M5p8b3, M5p8b4, M5p8b5, M5p8b6, M5p8b7, M5p8b10, M5p8b13, M5p8b19, M5p8b21, M5p8b25, M5p8b26, M5p8b27, M5p8b28, M5p8b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M5p8b3c0Ok, M5p8b4c0Ok, M5p8b5c0Ok, M5p8b6c0Ok, M5p8b7c0Ok, M5p8b10c0Ok, M5p8b10c1Ok, M5p8b10c2Ok, M5p8b13c0Ok, M5p8b19c0Ok, M5p8b21c0Ok, M5p8b25c0Ok, M5p8b26c0Ok, M5p8b27c0Ok, M5p8b28c0Ok, M5p8b31c0Ok]

def M5p9b10c0 : List Entry := [((0,0),[M5w26,M5w33,M5w58,M5w69,M5w81,M5w93])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5p9b10c0Ok : M5p9b10c0.all (testRow chart64 none M5t8 8) = true := by decide +kernel

def M5p9b10 : List Entry := M5p9b10c0
def M5g9 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], M5p9b10, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def M5t9 : Nat → List Entry := bucketOf M5g9
lemma M5v9 : verifiedR none 9 9 M5t9 := by
  apply checkedTier chart64 chart64Valid none (by decide) (by decide) M5v8
  apply checkBuckets
  simp only [M5g9, M5p9b10, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, M5p9b10c0Ok]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma M5Img : (fullRaw.toFinset.image restriction5.hom.fn).image can ⊆ insert zero M5Raw.toFinset := by decide +kernel

lemma M5LB {q} (h : Projection8403.Can q (fullRaw.toFinset.image restriction5.hom.fn)) : 10 ≤ q := by
  apply noCan M5Img M5Need ?_ h
  intro k lim live
  have eq := sortFinset M5Raw
  exact M5v9 (0,0) (sortSignals M5Raw) (hit_mem (by decide +kernel))
    (by decide +kernel) (by simp [preserve,resources]) k lim (eq.symm ▸ live)

def FRaw : List Sig := [(0x952455555554aaaaaaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75), (0xb36ecccccccd9999999b333666d9b36e,0x2c002c002c002c002c002c002c002c), (0xc38c0f0f0f0e1e1e1e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf), (0xc07cff00ff01fe01fe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0), (0xff80ffff0001fffe0003fff8001fff80,0x26002600260026002600260026002600), (0xfffffffe00000003ffffffe00000,0xb800b800b800b800b800b800b800b800), (0xfffffffffffffffc000000000000,0xc000c000c000c000c000c000c000c000)]

lemma FNeed : necessary FRaw := needFrom (pn := [(0,4), (2,6), (0,1), (2,2), (7,1), (21,1), (50,1)]) (by decide) (by decide +kernel)

def Fw0 : Sig := (0xe0000001c000000e00000,0xc80fc80fc80fc80fc80fc80fc80fc80f)
def Fw1 : Sig := (0xfe000001fc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw2 : Sig := (0x30200000604000018200000,0xc8c3c8c3c8c3c8c3c8c3c8c3c8c3c8c3)
def Fw3 : Sig := (0x30e0000061c000018e00000,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw4 : Sig := (0xf0e00001e1c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw5 : Sig := (0x333200006664000000000000,0xc000c000c000c000c000c000c000c000)
def Fw6 : Sig := (0xf0f00001e1e0000000000000,0x0)
def Fw7 : Sig := (0xfffe0001fffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw8 : Sig := (0xfffe0001fffc0007ffe00000,0xd800d800d800d800d800d800d800d800)
def Fw9 : Sig := (0xfffe0001ffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw10 : Sig := (0xf000e001e001c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw11 : Sig := (0x33003200660064000000000000,0xc000c000c000c000c000c000c000c000)
def Fw12 : Sig := (0xf000f001e001e0000000000000,0x0)
def Fw13 : Sig := (0xff000001fe0000000000000000,0x0)
def Fw14 : Sig := (0xff00fe01fe01fc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw15 : Sig := (0xff00fe01fe01fc03f807e00000,0xf800f800f800f800f800f800f800f800)
def Fw16 : Sig := (0xff00fe01fe01ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw17 : Sig := (0xfffffe01fffffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw18 : Sig := (0x101111002022220040088000000,0xff51ff51ff51ff51ff51ff51ff51ff51)
def Fw19 : Sig := (0x303030206060604000000000000,0xc000c000c000c000c000c000c000c000)
def Fw20 : Sig := (0xf0f00001e1e0000000000000000,0x0)
def Fw21 : Sig := (0xf0f0f0e1e1e1e1c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw22 : Sig := (0xf0f0f0e1e1e1e1c3c3878e00000,0xe800e800e800e800e800e800e800e800)
def Fw23 : Sig := (0xf0f0f0e1e1e1e1fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw24 : Sig := (0xf0ffffe1e1ffffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw25 : Sig := (0xf0ffffe1e1ffffc3c3fffe00000,0xf800f800f800f800f800f800f800f800)
def Fw26 : Sig := (0xfff0ffe1ffe1ffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw27 : Sig := (0x3030303060606060000000000000,0x0)
def Fw28 : Sig := (0x3333000066660000000000000000,0x0)
def Fw29 : Sig := (0x3333333266666664000000000000,0xc000c000c000c000c000c000c000c000)
def Fw30 : Sig := (0x3333333266666664ccc999200000,0xf800f800f800f800f800f800f800f800)
def Fw31 : Sig := (0x3333333266666667ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw32 : Sig := (0x3333fffe6667fffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw33 : Sig := (0x3333fffe6667fffccccfffe00000,0xf800f800f800f800f800f800f800f800)
def Fw34 : Sig := (0x33ff33fe67fe67fc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw35 : Sig := (0x33ff33fe67fe67fccff99fe00000,0xf800f800f800f800f800f800f800f800)
def Fw36 : Sig := (0x3f3f3f3e7e7e7e7c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw37 : Sig := (0xcccccccd99999998000000000000,0x0)
def Fw38 : Sig := (0xcccccccd9999999b333666c00000,0x0)
def Fw39 : Sig := (0xccccffff9999fffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw40 : Sig := (0xccffccff99ff99fc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw41 : Sig := (0xcfcfcfcf9f9f9f9c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw42 : Sig := (0xf0f0f0f1e1e1e1e0000000000000,0x0)
def Fw43 : Sig := (0xf0f0f0f1e1e1e1e3c3c787000000,0x10001000100010001000100010001000)
def Fw44 : Sig := (0xf0f0f0f1e1e1e1e3ffffffe00000,0x38003800380038003800380038003800)
def Fw45 : Sig := (0xf0f0ffffe1e1fffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw46 : Sig := (0xf0fff0ffe1ffe1fc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw47 : Sig := (0xf3f3f3f3e7e7e7e4000000000000,0xc000c000c000c000c000c000c000c000)
def Fw48 : Sig := (0xfcfcfcfdf9f9f9f8000000000000,0x0)
def Fw49 : Sig := (0xff00ff01fe01fe00000000000000,0x0)
def Fw50 : Sig := (0xff00ff01fe01fe03fc07f8000000,0x0)
def Fw51 : Sig := (0xff00fffffe01fffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw52 : Sig := (0xff00fffffe01fffffc07ffe00000,0xd800d800d800d800d800d800d800d800)
def Fw53 : Sig := (0xff0fff0ffe1ffe1c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw54 : Sig := (0xff33ff33fe67fe64000000000000,0xc000c000c000c000c000c000c000c000)
def Fw55 : Sig := (0xfff0fff1ffe1ffe0000000000000,0x0)
def Fw56 : Sig := (0xffff0001fffe0000000000000000,0x0)
def Fw57 : Sig := (0xffff0001fffe0003fff800000000,0x20002000200020002000200020002000)
def Fw58 : Sig := (0xffff0001fffe0003ffffffe00000,0x38003800380038003800380038003800)
def Fw59 : Sig := (0xffff00fffffe01fc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw60 : Sig := (0xffff0f0ffffe1e1c000000000000,0xc000c000c000c000c000c000c000c000)
def Fw61 : Sig := (0xffff3333fffe6664000000000000,0xc000c000c000c000c000c000c000c000)
def Fw62 : Sig := (0xffffcccdffff9998000000000000,0x0)
def Fw63 : Sig := (0xfffff0f1ffffe1e0000000000000,0x0)
def Fw64 : Sig := (0xffffff01fffffe00000000000000,0x0)
def Fw65 : Sig := (0xfffffffe00000003ffffffe00000,0xb800b800b800b800b800b800b800b800)
def Fw66 : Sig := (0xfffffffe000001ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw67 : Sig := (0xfffffffe00001e1fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw68 : Sig := (0xfffffffe00006667ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw69 : Sig := (0xfffffffe0001ffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw70 : Sig := (0xfffffffe001e001fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw71 : Sig := (0xfffffffe00660067ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw72 : Sig := (0xfffffffe01fe01ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw73 : Sig := (0xfffffffe01ffffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw74 : Sig := (0xfffffffe06060607ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw75 : Sig := (0xfffffffe1e1e1e1fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw76 : Sig := (0xfffffffe1e1fffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw77 : Sig := (0xfffffffe1ffe1fffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw78 : Sig := (0xfffffffe66666667ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw79 : Sig := (0xfffffffe6667ffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw80 : Sig := (0xfffffffe67fe67ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw81 : Sig := (0xfffffffe7e7e7e7fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw82 : Sig := (0xffffffff9999999bffffffe00000,0xb800b800b800b800b800b800b800b800)
def Fw83 : Sig := (0xffffffff9999ffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw84 : Sig := (0xffffffff99ff99ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw85 : Sig := (0xffffffff9f9f9f9fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw86 : Sig := (0xffffffffe1e1e1e3ffffffe00000,0xb800b800b800b800b800b800b800b800)
def Fw87 : Sig := (0xffffffffe1e1ffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw88 : Sig := (0xffffffffe1ffe1ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw89 : Sig := (0xffffffffe7e7e7e7ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw90 : Sig := (0xfffffffffe01fe03ffffffe00000,0xb800b800b800b800b800b800b800b800)
def Fw91 : Sig := (0xfffffffffe01ffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw92 : Sig := (0xfffffffffe1ffe1fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw93 : Sig := (0xfffffffffe67fe67ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw94 : Sig := (0xfffffffffffe0003ffffffe00000,0xb800b800b800b800b800b800b800b800)
def Fw95 : Sig := (0xfffffffffffe01ffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw96 : Sig := (0xfffffffffffe1e1fffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw97 : Sig := (0xfffffffffffe6667ffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw98 : Sig := (0xfffffffffffffffc000000000000,0xc000c000c000c000c000c000c000c000)
def Fw99 : Sig := (0xffffffffffffffff333666c00000,0xc000c000c000c000c000c000c000c000)
def Fw100 : Sig := (0xfffffffffffffffffc07f8000000,0xc000c000c000c000c000c000c000c000)
def Fw101 : Sig := (0xffffffffffffffffffffffe00000,0xf800f800f800f800f800f800f800f800)
def Fw102 : Sig := (0xc0000000000000000000078e0000c,0x8cf08cf08cf08cf08cf08cf08cf08cf)
def Fw103 : Sig := (0xc00000f0e00001e1c000078e0000c,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw104 : Sig := (0xc0000fffe0001fffc000078e0000c,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw105 : Sig := (0xc0f0f0f0e1e1e1e1c000078e0000c,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw106 : Sig := (0xcfffffffffffffffc000078e0000c,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw107 : Sig := (0x24010155540202aaa80402aa400024,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw108 : Sig := (0x6e0000000000000000000666c0006e,0x2c002c002c002c002c002c002c002c)
def Fw109 : Sig := (0x6e0000cccc00019998000666c0006e,0x2c002c002c002c002c002c002c002c)
def Fw110 : Sig := (0x6e0000cfce00019f9c00067ee0006e,0xc8efc8efc8efc8efc8efc8efc8efc8ef)
def Fw111 : Sig := (0x6e0000fffe0001fffc000666c0006e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw112 : Sig := (0x6efffffffffffffffc000666c0006e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw113 : Sig := (0x70f000f001e001e003c007801e0070,0x1000100010001000100010001000100)
def Fw114 : Sig := (0x70f0f0f0f1e1e1e1e3c007801e0070,0x1000100010001000100010001000100)
def Fw115 : Sig := (0x70ffffffffffffffffc007801e0070,0xc100c100c100c100c100c100c100c100)
def Fw116 : Sig := (0x7c00000000000000000007f800007c,0x1c001c001c001c001c001c001c001c0)
def Fw117 : Sig := (0x7c0000ff000001fe000007f800007c,0x1c001c001c001c001c001c001c001c0)
def Fw118 : Sig := (0x7c0000ff0e0001fe1c0007f8e0007c,0xc9cfc9cfc9cfc9cfc9cfc9cfc9cfc9cf)
def Fw119 : Sig := (0x7c0000fffe0001fffc0007f800007c,0xc1c0c1c0c1c0c1c0c1c0c1c0c1c0c1c0)
def Fw120 : Sig := (0x7cff00ff01fe01fe03fc07f800007c,0x1c001c001c001c001c001c001c001c0)
def Fw121 : Sig := (0x7cfffffffffffffffc0007f800007c,0xc1c0c1c0c1c0c1c0c1c0c1c0c1c0c1c0)
def Fw122 : Sig := (0x800003000200060004000800200080,0xea03ea03ea03ea03ea03ea03ea03ea03)
def Fw123 : Sig := (0x3800000000000000000003800e00380,0x2a0f2a0f2a0f2a0f2a0f2a0f2a0f2a0f)
def Fw124 : Sig := (0x380000f0000001e0000003800000380,0x22002200220022002200220022002200)
def Fw125 : Sig := (0x380000f000e001e001c003800e00380,0xea0fea0fea0fea0fea0fea0fea0fea0f)
def Fw126 : Sig := (0x38000ff00fe01fe01fc003800e00380,0xea0fea0fea0fea0fea0fea0fea0fea0f)
def Fw127 : Sig := (0x3800f0f0f0e1e1e1e1c003800e00380,0xea0fea0fea0fea0fea0fea0fea0fea0f)
def Fw128 : Sig := (0x380fffffffffffffffc003800e00380,0xea0fea0fea0fea0fea0fea0fea0fea0f)
def Fw129 : Sig := (0x38c000f0f0e001e1e1c003878e0038c,0xeacfeacfeacfeacfeacfeacfeacfeacf)
def Fw130 : Sig := (0x4000000111000002220444088020400,0xff51ff51ff51ff51ff51ff51ff51ff51)
def Fw131 : Sig := (0x4000101010002020200444088020400,0xff51ff51ff51ff51ff51ff51ff51ff51)
def Fw132 : Sig := (0x424000055540000aaa84442aa420424,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw133 : Sig := (0x424111155542222aaa84442aa420424,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw134 : Sig := (0xc003030000060600000c0c000060c00,0x0)
def Fw135 : Sig := (0xc00fffffffffffffffcc0c000060c00,0xc000c000c000c000c000c000c000c000)
def Fw136 : Sig := (0xc80003300000066000000c800000c80,0x22002200220022002200220022002200)
def Fw137 : Sig := (0x142051515150a2a2a2a145428a0a1420,0xff71ff71ff71ff71ff71ff71ff71ff71)
def Fw138 : Sig := (0x15001155115422aa22a845508a421500,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw139 : Sig := (0x3062c0c0c0c181818183030606183062,0x200020002000200020002000200020)
def Fw140 : Sig := (0x3062f0f0f0f1e1e1e1e3030606183062,0x200020002000200020002000200020)
def Fw141 : Sig := (0x3062ffffffffffffffff030606183062,0xc020c020c020c020c020c020c020c020)
def Fw142 : Sig := (0x330200cc00cc01980198033006c03302,0x2c002c002c002c002c002c002c002c)
def Fw143 : Sig := (0x330200ff00fe01fe01fc033006c03302,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw144 : Sig := (0x330200ff00fe01fe01fc03f807e03302,0xf82cf82cf82cf82cf82cf82cf82cf82c)
def Fw145 : Sig := (0x3302fffffffffffffffc033006c03302,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw146 : Sig := (0x338200cf00ce019e019c033806e03382,0xea2fea2fea2fea2fea2fea2fea2fea2f)
def Fw147 : Sig := (0x3c000000000000000003c3c0001e3c00,0x0)
def Fw148 : Sig := (0x3c00f0f00001e1e00003c3c0001e3c00,0x0)
def Fw149 : Sig := (0x3c00f0f0f0f1e1e1e1e3c3c0001e3c00,0x0)
def Fw150 : Sig := (0x3c00ffff0001fffe0003c3c0001e3c00,0x0)
def Fw151 : Sig := (0x3c00ffffffffe1e00003fffffffe3c00,0xb800b800b800b800b800b800b800b800)
def Fw152 : Sig := (0x3c00ffffffffffffffffc3c0001e3c00,0xc000c000c000c000c000c000c000c000)
def Fw153 : Sig := (0x3c00fffffffffffffffffffffffe3c00,0xf800f800f800f800f800f800f800f800)
def Fw154 : Sig := (0x3c0cf0f00f0fe1e01e1fc3c078fe3c0c,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw155 : Sig := (0x3c62f0f0c0c1e1e18183c3c6061e3c62,0x200020002000200020002000200020)
def Fw156 : Sig := (0x3c70f0f0f001e1e1e003c3c7801e3c70,0x1000100010001000100010001000100)
def Fw157 : Sig := (0x3f80000000000000000003f800003f80,0x22002200220022002200220022002200)
def Fw158 : Sig := (0x3f800000000000000003ffffffe03f80,0x3a003a003a003a003a003a003a003a00)
def Fw159 : Sig := (0x3f8000ff000001fe000003f800003f80,0x22002200220022002200220022002200)
def Fw160 : Sig := (0x3f8000ff000e01fe001c03f800e03f80,0xea0fea0fea0fea0fea0fea0fea0fea0f)
def Fw161 : Sig := (0x3f8000ff00fe01fe01fc03f800003f80,0xe200e200e200e200e200e200e200e200)
def Fw162 : Sig := (0x3f80f0ff0001e1fe0003c3f8001e3f80,0x22002200220022002200220022002200)
def Fw163 : Sig := (0x3f80ffff0001fffe000003f800003f80,0x22002200220022002200220022002200)
def Fw164 : Sig := (0x3f80fffffffe01fe0003ffffffe03f80,0xba00ba00ba00ba00ba00ba00ba00ba00)
def Fw165 : Sig := (0x3f80fffffffe01fe01ffffffffe03f80,0xfa00fa00fa00fa00fa00fa00fa00fa00)
def Fw166 : Sig := (0x3f80fffffffffffffffc03f800003f80,0xe200e200e200e200e200e200e200e200)
def Fw167 : Sig := (0x3f80ffffffffffffffffffffffe03f80,0xfa00fa00fa00fa00fa00fa00fa00fa00)
def Fw168 : Sig := (0x3f8200ff00cc01fe019803f806c03f82,0x222c222c222c222c222c222c222c222c)
def Fw169 : Sig := (0x40103300330066006600cc0198064010,0x5c005c005c005c005c005c005c005c0)
def Fw170 : Sig := (0x40103333333266666664cc0198064010,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw171 : Sig := (0x4010fffffffffffffffccc0198064010,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw172 : Sig := (0x407c3300ff006601fe00cc07f806407c,0x5c005c005c005c005c005c005c005c0)
def Fw173 : Sig := (0x408000000000000000000c0818204080,0x2ec32ec32ec32ec32ec32ec32ec32ec3)
def Fw174 : Sig := (0x408003030000060600000c0800004080,0x26002600260026002600260026002600)
def Fw175 : Sig := (0x408003030302060606040c0818204080,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw176 : Sig := (0x40800f0f0f0e1e1e1e1c0c0818204080,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw177 : Sig := (0x408033333332666666640c0818204080,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw178 : Sig := (0x4080fffffffffffffffc0c0818204080,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw179 : Sig := (0x408c00000f0e00001e1c0c0878e0408c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw180 : Sig := (0x408c03030f0e06061e1c0c0878e0408c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw181 : Sig := (0x40903303330266066604cc0998264090,0xefc3efc3efc3efc3efc3efc3efc3efc3)
def Fw182 : Sig := (0x438000000000000000000c3818e04380,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw183 : Sig := (0x4380030f030e061e061c0c3818e04380,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw184 : Sig := (0x4c800000000000000000ccc800064c80,0x26002600260026002600260026002600)
def Fw185 : Sig := (0x4c803333000066660000ccc800064c80,0x26002600260026002600260026002600)
def Fw186 : Sig := (0x4c803333030266660604ccc818264c80,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw187 : Sig := (0x4c803333333266666664ccc800064c80,0xe600e600e600e600e600e600e600e600)
def Fw188 : Sig := (0x4c80ffff0001fffe0000ccc800064c80,0x26002600260026002600260026002600)
def Fw189 : Sig := (0x4c80fffffffffffffffcccc800064c80,0xe600e600e600e600e600e600e600e600)
def Fw190 : Sig := (0x4c903333330066666600ccc998064c90,0x27c027c027c027c027c027c027c027c0)
def Fw191 : Sig := (0x7c80f3f30001e7e60003cfc8001e7c80,0x26002600260026002600260026002600)
def Fw192 : Sig := (0x7f8033ff000067fe0000cff800067f80,0x26002600260026002600260026002600)
def Fw193 : Sig := (0x806ccc00cc019801980330066019806c,0x0)
def Fw194 : Sig := (0x806cff00ff01fe01fe03fc07f819806c,0x0)
def Fw195 : Sig := (0x806cffffffff98019803fffffff9806c,0xb800b800b800b800b800b800b800b800)
def Fw196 : Sig := (0x806cffffffffffffffff30066019806c,0xc000c000c000c000c000c000c000c000)
def Fw197 : Sig := (0x806cfffffffffffffffffffffff9806c,0xf800f800f800f800f800f800f800f800)
def Fw198 : Sig := (0x8124000055540000aaa81412aa408124,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw199 : Sig := (0x8124050505040a0a0a081412aa408124,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw200 : Sig := (0x8124050555540a0aaaa81412aa408124,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw201 : Sig := (0x812455555554aaaaaaa81412aa408124,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw202 : Sig := (0x830c0c0c0c0c18181818303060c1830c,0xc000c000c000c000c000c000c000c)
def Fw203 : Sig := (0x830c0c0c0f0e18181e1c303078e1830c,0xc8cfc8cfc8cfc8cfc8cfc8cfc8cfc8cf)
def Fw204 : Sig := (0x830c0f0f0f0e1e1e1e1c303060c1830c,0xc00cc00cc00cc00cc00cc00cc00cc00c)
def Fw205 : Sig := (0x830cfffffffffffffffc303060c1830c,0xc00cc00cc00cc00cc00cc00cc00cc00c)
def Fw206 : Sig := (0x836e0c0ccccc18199998303666c1836e,0x2c002c002c002c002c002c002c002c)
def Fw207 : Sig := (0x838c0c0f0c0e181e181c303860e1838c,0xea0fea0fea0fea0fea0fea0fea0fea0f)
def Fw208 : Sig := (0x9124454555548a8aaaa91512aa489124,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw209 : Sig := (0x952400000054000000a95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw210 : Sig := (0x95240000050400000a095552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw211 : Sig := (0x952400001110000022215552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw212 : Sig := (0x9524000055540000aaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw213 : Sig := (0x952400050004000a00095552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw214 : Sig := (0x95240055005400aa00a80150024a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw215 : Sig := (0x95240055005400aa00a95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw216 : Sig := (0x952401010100020202015552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw217 : Sig := (0x9524050505040a0a0a095552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw218 : Sig := (0x952411111110222222204440880a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw219 : Sig := (0x952411111110222222215552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw220 : Sig := (0x9524444455548888aaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw221 : Sig := (0x9524454545448a8a8a895552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw222 : Sig := (0x952450505554a0a0aaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw223 : Sig := (0x952455005554aa00aaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw224 : Sig := (0x952455055504aa0aaa095552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw225 : Sig := (0x952455550504aaaa0a095552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw226 : Sig := (0x952455555554aaaaaaa95552aa4a9524,0xff75ff75ff75ff75ff75ff75ff75ff75)
def Fw227 : Sig := (0xb300cccc00019998000333300019b300,0x0)
def Fw228 : Sig := (0xb300ffff0001fffe000333300019b300,0x0)
def Fw229 : Sig := (0xb300ffffffff99980003fffffff9b300,0xb800b800b800b800b800b800b800b800)
def Fw230 : Sig := (0xb300ffffffffffffffff33300019b300,0xc000c000c000c000c000c000c000c000)
def Fw231 : Sig := (0xb300fffffffffffffffffffffff9b300,0xf800f800f800f800f800f800f800f800)
def Fw232 : Sig := (0xb36e000000000000000000000019b36e,0x2c002c002c002c002c002c002c002c)
def Fw233 : Sig := (0xb36e0000000000000003333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw234 : Sig := (0xb36e0000cccc0001999b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw235 : Sig := (0xb36e00cc00cc01980198033006d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw236 : Sig := (0xb36e00cc00cc0198019b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw237 : Sig := (0xb36e0c0c0c0c1818181b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw238 : Sig := (0xb36e3333333266666667333666d9b36e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw239 : Sig := (0xb36ecccccccd9999999b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw240 : Sig := (0xb36ecccccfcf99999f9f33367ef9b36e,0xc8efc8efc8efc8efc8efc8efc8efc8ef)
def Fw241 : Sig := (0xb36eccccfcfd9999f9fb333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw242 : Sig := (0xb36eccccffff9999ffff333666d9b36e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw243 : Sig := (0xb36eccfcccfd99f999fb333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw244 : Sig := (0xb36eccffcccd99ff999b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw245 : Sig := (0xb36eccffccff99ff99ff333666d9b36e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw246 : Sig := (0xb36ecfcfcccd9f9f999b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw247 : Sig := (0xb36ecfcfcfcf9f9f9f9f333666d9b36e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw248 : Sig := (0xb36efcfcfcfdf9f9f9fb333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw249 : Sig := (0xb36effccffcdff99ff9b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw250 : Sig := (0xb36effccffcdff99ff9bff37fed9b36e,0x2c002c002c002c002c002c002c002c)
def Fw251 : Sig := (0xb36efffcfffdfff9fffb333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw252 : Sig := (0xb36effffcccdffff999b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw253 : Sig := (0xb36efffffcfdfffff9fb333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw254 : Sig := (0xb36effffffcdffffff9b333666d9b36e,0x2c002c002c002c002c002c002c002c)
def Fw255 : Sig := (0xb36efffffffffffffffc00000019b36e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw256 : Sig := (0xb36effffffffffffffff333666d9b36e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw257 : Sig := (0xb36efffffffffffffffffffffff9b36e,0xf82cf82cf82cf82cf82cf82cf82cf82c)
def Fw258 : Sig := (0xb3eecccfcccf999f999f333e66f9b3ee,0xea2fea2fea2fea2fea2fea2fea2fea2f)
def Fw259 : Sig := (0xbf00fcfc0001f9f80003f3f0001fbf00,0x0)
def Fw260 : Sig := (0xbf00fffffffffffffffff3f0001fbf00,0xc000c000c000c000c000c000c000c000)
def Fw261 : Sig := (0xbf6ecccccccd9999999bf3f666dfbf6e,0x2c002c002c002c002c002c002c002c)
def Fw262 : Sig := (0xbf6efcfccccdf9f9999bf3f666dfbf6e,0x2c002c002c002c002c002c002c002c)
def Fw263 : Sig := (0xbf6efcfcfcfdf9f9f9fbf3f666dfbf6e,0x2c002c002c002c002c002c002c002c)
def Fw264 : Sig := (0xbf6effffcccdffff999bf3f666dfbf6e,0x2c002c002c002c002c002c002c002c)
def Fw265 : Sig := (0xbf6efffffffffffffffff3f666dfbf6e,0xc02cc02cc02cc02cc02cc02cc02cc02c)
def Fw266 : Sig := (0xbf80ccff000199fe000333f80019bf80,0x22002200220022002200220022002200)
def Fw267 : Sig := (0xbfeeccffcccd99ff999b33fe66d9bfee,0x222c222c222c222c222c222c222c222c)
def Fw268 : Sig := (0xc000ff000001fe000003fc00001fc000,0x4000400040004000400040004000400)
def Fw269 : Sig := (0xc000ffff0001fffe0003fc00001fc000,0x4000400040004000400040004000400)
def Fw270 : Sig := (0xc000fffffffffffffffffc00001fc000,0xc400c400c400c400c400c400c400c400)
def Fw271 : Sig := (0xc00c0f000f001e001e003c007801c00c,0x4c004c004c004c004c004c004c004c0)
def Fw272 : Sig := (0xc00c0f000f0e1e001e1c3c0078e1c00c,0xcccfcccfcccfcccfcccfcccfcccfcccf)
def Fw273 : Sig := (0xc00c0f0f0f0e1e1e1e1c3c007801c00c,0xc4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0)
def Fw274 : Sig := (0xc00cfffffffffffffffc3c007801c00c,0xc4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0)
def Fw275 : Sig := (0xc07c00000000000000000000001fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw276 : Sig := (0xc07c0000000000000003fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw277 : Sig := (0xc07c0000ff000001fe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw278 : Sig := (0xc07c0f000f001e001e03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw279 : Sig := (0xc07c0f00ff001e01fe003c07f801c07c,0x5c005c005c005c005c005c005c005c0)
def Fw280 : Sig := (0xc07c3300330066006600cc01981fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw281 : Sig := (0xc07c3300330066006603fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw282 : Sig := (0xc07cff00ff01fe01fe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw283 : Sig := (0xc07cff00ff0ffe01fe1ffc07f8ffc07c,0xcdcfcdcfcdcfcdcfcdcfcdcfcdcfcdcf)
def Fw284 : Sig := (0xc07cff00fff1fe01ffe3fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw285 : Sig := (0xc07cff00fffffe01fffffc07f81fc07c,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw286 : Sig := (0xc07cff0fff01fe1ffe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw287 : Sig := (0xc07cff0fff0ffe1ffe1ffc07f81fc07c,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw288 : Sig := (0xc07cff30ff31fe61fe63fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw289 : Sig := (0xc07cff33ff01fe67fe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw290 : Sig := (0xc07cff33ff33fe67fe67fc07f81fc07c,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw291 : Sig := (0xc07cffccffcdff99ff9bfc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw292 : Sig := (0xc07cffccffcdff99ff9bff37fedfc07c,0x5c005c005c005c005c005c005c005c0)
def Fw293 : Sig := (0xc07cfff0fff1ffe1ffe3fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw294 : Sig := (0xc07cfffcfffdfff9fffbfc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw295 : Sig := (0xc07cffffff01fffffe03fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw296 : Sig := (0xc07cffffffcdffffff9bfc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw297 : Sig := (0xc07cfffffff1ffffffe3fc07f81fc07c,0x5c005c005c005c005c005c005c005c0)
def Fw298 : Sig := (0xc07cfffffffffffffffc0000001fc07c,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw299 : Sig := (0xc07cfffffffffffffffffc07f81fc07c,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw300 : Sig := (0xc07cffffffffffffffffffffffffc07c,0xfdc0fdc0fdc0fdc0fdc0fdc0fdc0fdc0)
def Fw301 : Sig := (0xc08c0f030f021e061e043c087821c08c,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw302 : Sig := (0xc0fcff03ff03fe07fe07fc0ff83fc0fc,0xefc3efc3efc3efc3efc3efc3efc3efc3)
def Fw303 : Sig := (0xc38000000000000000003c380001c380,0x26002600260026002600260026002600)
def Fw304 : Sig := (0xc3800f0f00001e1e00003c380001c380,0x26002600260026002600260026002600)
def Fw305 : Sig := (0xc3800f0f000e1e1e001c3c3800e1c380,0xee0fee0fee0fee0fee0fee0fee0fee0f)
def Fw306 : Sig := (0xc3800f0f03021e1e06043c381821c380,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw307 : Sig := (0xc3800f0f0f0e1e1e1e1c3c380001c380,0xe600e600e600e600e600e600e600e600)
def Fw308 : Sig := (0xc380ff0f0001fe1e0003fc38001fc380,0x26002600260026002600260026002600)
def Fw309 : Sig := (0xc380ffff0001fffe00003c380001c380,0x26002600260026002600260026002600)
def Fw310 : Sig := (0xc380fffffffffffffffc3c380001c380,0xe600e600e600e600e600e600e600e600)
def Fw311 : Sig := (0xc38c000000000000000000000001c38c,0x6cf06cf06cf06cf06cf06cf06cf06cf)
def Fw312 : Sig := (0xc38c00000000000000003c3878e1c38c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw313 : Sig := (0xc38c0000000000000003ffffffe1c38c,0x3ecf3ecf3ecf3ecf3ecf3ecf3ecf3ecf)
def Fw314 : Sig := (0xc38c0000000e0000001c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw315 : Sig := (0xc38c00000302000006043c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw316 : Sig := (0xc38c00000f0e00001e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw317 : Sig := (0xc38c000f000e001e001c003800e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw318 : Sig := (0xc38c000f000e001e001c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw319 : Sig := (0xc38c03030302060606040c081821c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw320 : Sig := (0xc38c03030302060606043c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw321 : Sig := (0xc38c0c0c0c0c181818183c3878e1c38c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw322 : Sig := (0xc38c0c0c0f0e18181e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw323 : Sig := (0xc38c0f000f001e001e003c3878e1c38c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw324 : Sig := (0xc38c0f000f0e1e001e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw325 : Sig := (0xc38c0f0f00001e1e00003c3878e1c38c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw326 : Sig := (0xc38c0f0f0c0c1e1e18183c3860c1c38c,0x260c260c260c260c260c260c260c260c)
def Fw327 : Sig := (0xc38c0f0f0f001e1e1e003c387801c38c,0x26c026c026c026c026c026c026c026c0)
def Fw328 : Sig := (0xc38c0f0f0f0e1e1e1e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw329 : Sig := (0xc38c0f0ffffe1e1ffffc3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw330 : Sig := (0xc38c0fff0ffe1ffe1ffc3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw331 : Sig := (0xc38c3f3f3f3e7e7e7e7c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw332 : Sig := (0xc38ccfcfcfcf9f9f9f9c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw333 : Sig := (0xc38ccfcfcfcf9f9f9f9f3f3e7ee1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw334 : Sig := (0xc38cf0f0f0f1e1e1e1e03c3878e1c38c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw335 : Sig := (0xc38cff0f0f0ffe1e1e1ffc3878ffc38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw336 : Sig := (0xc38cff0fff0ffe1ffe1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw337 : Sig := (0xc38cff0fff0ffe1ffe1ffc3ff8e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw338 : Sig := (0xc38cffff0f0ffffe1e1c3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw339 : Sig := (0xc38cfffffffffffffffc00000001c38c,0xc6cfc6cfc6cfc6cfc6cfc6cfc6cfc6cf)
def Fw340 : Sig := (0xc38cfffffffffffffffc3c3878e1c38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw341 : Sig := (0xc38cffffffffffffffffffffffe1c38c,0xfecffecffecffecffecffecffecffecf)
def Fw342 : Sig := (0xc39c3f0f3f0e7e1e7e1cfc39f8e7c39c,0xefcfefcfefcfefcfefcfefcfefcfefcf)
def Fw343 : Sig := (0xc3eccf0fcf0f9e1f9e1f3c3e78f9c3ec,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw344 : Sig := (0xc3ee0f0fcfce1e1f9f9c3c3e7ee1c3ee,0xeeefeeefeeefeeefeeefeeefeeefeeef)
def Fw345 : Sig := (0xc3fc0000000000000003fc3ff8ffc3fc,0x2fcf2fcf2fcf2fcf2fcf2fcf2fcf2fcf)
def Fw346 : Sig := (0xc3fc0f0f0f0e1e1e1e1ffc3ff8ffc3fc,0xefcfefcfefcfefcfefcfefcfefcfefcf)
def Fw347 : Sig := (0xc3fc0f0fff0e1e1ffe1c3c3ff8e1c3fc,0xefcfefcfefcfefcfefcfefcfefcfefcf)
def Fw348 : Sig := (0xc3fcff00ff01fe01fe03fc3ff8ffc3fc,0x2fcf2fcf2fcf2fcf2fcf2fcf2fcf2fcf)
def Fw349 : Sig := (0xc3fcff0fff01fe1ffe03fc3ff81fc3fc,0x27c027c027c027c027c027c027c027c0)
def Fw350 : Sig := (0xc3fcff0fff0ffe1ffe1ffc3ff8ffc3fc,0xefcfefcfefcfefcfefcfefcfefcfefcf)
def Fw351 : Sig := (0xc3fcfffffffffffffffffc3ff8ffc3fc,0xefcfefcfefcfefcfefcfefcfefcfefcf)
def Fw352 : Sig := (0xcc80ff330001fe660003fcc8001fcc80,0x26002600260026002600260026002600)
def Fw353 : Sig := (0xccfcff33ff01fe67fe03fccff81fccfc,0x27c027c027c027c027c027c027c027c0)
def Fw354 : Sig := (0xcf803f3f00007e7e0000fcf80007cf80,0x26002600260026002600260026002600)
def Fw355 : Sig := (0xcf8c3f3f0f0e7e7e1e1cfcf878e7cf8c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw356 : Sig := (0xf37cffccff01ff99fe03ff37f81ff37c,0x5c005c005c005c005c005c005c005c0)
def Fw357 : Sig := (0xf37cffffff01fffffe03ff37f81ff37c,0x5c005c005c005c005c005c005c005c0)
def Fw358 : Sig := (0xf37effccffcdff99ff9bff37fedff37e,0x5ec05ec05ec05ec05ec05ec05ec05ec)
def Fw359 : Sig := (0xf37effffffffffffffffff37fedff37e,0xc5ecc5ecc5ecc5ecc5ecc5ecc5ecc5ec)
def Fw360 : Sig := (0xf380cfcf00019f9e00033f380019f380,0x26002600260026002600260026002600)
def Fw361 : Sig := (0xf38ccfcf0f0f9f9e1e1f3f3878f9f38c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw362 : Sig := (0xf38e0fcf0fce1f9e1f9c3f387ee1f38e,0xeeefeeefeeefeeefeeefeeefeeefeeef)
def Fw363 : Sig := (0xf3ee00000000000000033f3e7ef9f3ee,0x2eef2eef2eef2eef2eef2eef2eef2eef)
def Fw364 : Sig := (0xf3ee0f0f0f0e1e1e1e1f3f3e7ef9f3ee,0xeeefeeefeeefeeefeeefeeefeeefeeef)
def Fw365 : Sig := (0xf3eecccccccd9999999b3f3e7ef9f3ee,0x2eef2eef2eef2eef2eef2eef2eef2eef)
def Fw366 : Sig := (0xf3eecfcfcccd9f9f999b3f3e66d9f3ee,0x262c262c262c262c262c262c262c262c)
def Fw367 : Sig := (0xf3eecfcfcfcf9f9f9f9f3f3e7ef9f3ee,0xeeefeeefeeefeeefeeefeeefeeefeeef)
def Fw368 : Sig := (0xf3eeffffffffffffffff3f3e7ef9f3ee,0xeeefeeefeeefeeefeeefeeefeeefeeef)
def Fw369 : Sig := (0xf3feffcfffcfff9fff9fff3ffefff3fe,0xefefefefefefefefefefefefefefefef)
def Fw370 : Sig := (0xfc00fff00001ffe00003ffc0001ffc00,0x4000400040004000400040004000400)
def Fw371 : Sig := (0xfc7cfff0ff01ffe1fe03ffc7f81ffc7c,0x5c005c005c005c005c005c005c005c0)
def Fw372 : Sig := (0xfc7cfff0fff1ffe1ffe3ffc7f81ffc7c,0x5c005c005c005c005c005c005c005c0)
def Fw373 : Sig := (0xfc7cffffff01fffffe03ffc7f81ffc7c,0x5c005c005c005c005c005c005c005c0)
def Fw374 : Sig := (0xfc7cffffffffffffffffffc7f81ffc7c,0xc5c0c5c0c5c0c5c0c5c0c5c0c5c0c5c0)
def Fw375 : Sig := (0xff8000000000000000000000001fff80,0x6000600060006000600060006000600)
def Fw376 : Sig := (0xff800000000000000003fff8001fff80,0x26002600260026002600260026002600)
def Fw377 : Sig := (0xff800000000000000003ffffffffff80,0x3e003e003e003e003e003e003e003e00)
def Fw378 : Sig := (0xff800000fffe0001fffffff8001fff80,0xe600e600e600e600e600e600e600e600)
def Fw379 : Sig := (0xff8000ff000001fe000003f8001fff80,0x26002600260026002600260026002600)
def Fw380 : Sig := (0xff8000ff000001fe0003fff8001fff80,0x26002600260026002600260026002600)
def Fw381 : Sig := (0xff800f0f00001e1e0003fff8001fff80,0x26002600260026002600260026002600)
def Fw382 : Sig := (0xff800fff00001ffe00003ff80001ff80,0x26002600260026002600260026002600)
def Fw383 : Sig := (0xff803333000066660000ccc8001fff80,0x26002600260026002600260026002600)
def Fw384 : Sig := (0xff803333000066660003fff8001fff80,0x26002600260026002600260026002600)
def Fw385 : Sig := (0xff80cccc000199980003fff8001fff80,0x26002600260026002600260026002600)
def Fw386 : Sig := (0xff80f0f00001e1e00003fff8001fff80,0x26002600260026002600260026002600)
def Fw387 : Sig := (0xff80ff000001fe000003fff8001fff80,0x26002600260026002600260026002600)
def Fw388 : Sig := (0xff80ffff0001fffe0003fff8001fff80,0x26002600260026002600260026002600)
def Fw389 : Sig := (0xff80ffff000ffffe001ffff800ffff80,0xee0fee0fee0fee0fee0fee0fee0fee0f)
def Fw390 : Sig := (0xff80ffff00f1fffe01e3fff8001fff80,0x26002600260026002600260026002600)
def Fw391 : Sig := (0xff80ffff00fffffe01fffff8001fff80,0xe600e600e600e600e600e600e600e600)
def Fw392 : Sig := (0xff80ffff0303fffe0607fff8183fff80,0xeec3eec3eec3eec3eec3eec3eec3eec3)
def Fw393 : Sig := (0xff80ffff0f0ffffe1e1ffff8001fff80,0xe600e600e600e600e600e600e600e600)
def Fw394 : Sig := (0xff80ffff3031fffe6063fff8001fff80,0x26002600260026002600260026002600)
def Fw395 : Sig := (0xff80ffff3333fffe6667fff8001fff80,0xe600e600e600e600e600e600e600e600)
def Fw396 : Sig := (0xff80ffffcccdffff999bfff8001fff80,0x26002600260026002600260026002600)
def Fw397 : Sig := (0xff80ffffcccdffff999bfffe66dfff80,0x26002600260026002600260026002600)
def Fw398 : Sig := (0xff80fffff0f1ffffe1e3fff8001fff80,0x26002600260026002600260026002600)
def Fw399 : Sig := (0xff80fffffcfdfffff9fbfff8001fff80,0x26002600260026002600260026002600)
def Fw400 : Sig := (0xff80ffffff01fffffe03fff8001fff80,0x26002600260026002600260026002600)
def Fw401 : Sig := (0xff80ffffff01fffffe03fffff81fff80,0x26002600260026002600260026002600)
def Fw402 : Sig := (0xff80fffffff1ffffffe3fff8001fff80,0x26002600260026002600260026002600)
def Fw403 : Sig := (0xff80fffffffffffffffc0000001fff80,0xc600c600c600c600c600c600c600c600)
def Fw404 : Sig := (0xff80fffffffffffffffffff8001fff80,0xe600e600e600e600e600e600e600e600)
def Fw405 : Sig := (0xff80ffffffffffffffffffffffffff80,0xfe00fe00fe00fe00fe00fe00fe00fe00)
def Fw406 : Sig := (0xff82ffff00cdfffe019bfff806dfff82,0x262c262c262c262c262c262c262c262c)
def Fw407 : Sig := (0xff8c0000000000000003fff878ffff8c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw408 : Sig := (0xff8c0f0f0f0e1e1e1e1ffff878ffff8c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw409 : Sig := (0xff8c0fff0f0e1ffe1e1c3ff878e1ff8c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw410 : Sig := (0xff8cffff0001fffe0003fff878ffff8c,0x2ecf2ecf2ecf2ecf2ecf2ecf2ecf2ecf)
def Fw411 : Sig := (0xff8cffff0c0dfffe181bfff860dfff8c,0x260c260c260c260c260c260c260c260c)
def Fw412 : Sig := (0xff8cffff0f01fffe1e03fff8781fff8c,0x26c026c026c026c026c026c026c026c0)
def Fw413 : Sig := (0xff8cffff0f0ffffe1e1ffff878ffff8c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw414 : Sig := (0xff8cfffffffffffffffffff878ffff8c,0xeecfeecfeecfeecfeecfeecfeecfeecf)
def Fw415 : Sig := (0xff90ffff3301fffe6603fff9981fff90,0x27c027c027c027c027c027c027c027c0)
def Fw416 : Sig := (0xffe2ffffc0c1ffff8183fffe061fffe2,0x26202620262026202620262026202620)
def Fw417 : Sig := (0xffecffffcc01ffff9803fffe601fffec,0x26002600260026002600260026002600)
def Fw418 : Sig := (0xffecfffffffffffffffffffe601fffec,0xe600e600e600e600e600e600e600e600)
def Fw419 : Sig := (0xffee0000000000000003fffe66dfffee,0x262c262c262c262c262c262c262c262c)
def Fw420 : Sig := (0xffeecccccccd9999999bfffe66dfffee,0x262c262c262c262c262c262c262c262c)
def Fw421 : Sig := (0xffeeffff0001fffe0003fff8001fffee,0x262c262c262c262c262c262c262c262c)
def Fw422 : Sig := (0xffeeffff0001fffe0003fffe66dfffee,0x262c262c262c262c262c262c262c262c)
def Fw423 : Sig := (0xffeeffffcccdffff999bfffe66dfffee,0x262c262c262c262c262c262c262c262c)
def Fw424 : Sig := (0xffeeffffcfcfffff9f9ffffe7effffee,0xeeefeeefeeefeeefeeefeeefeeefeeef)
def Fw425 : Sig := (0xffeefffffcfdfffff9fbfffe66dfffee,0x262c262c262c262c262c262c262c262c)
def Fw426 : Sig := (0xffeefffffffffffffffffffe66dfffee,0xe62ce62ce62ce62ce62ce62ce62ce62c)
def Fw427 : Sig := (0xfff0fffff001ffffe003ffff801ffff0,0x27002700270027002700270027002700)
def Fw428 : Sig := (0xfffc0000000000000003fffff81ffffc,0x27c027c027c027c027c027c027c027c0)
def Fw429 : Sig := (0xfffcff00ff01fe01fe03fc07f81ffffc,0x7c007c007c007c007c007c007c007c0)
def Fw430 : Sig := (0xfffcff00ff01fe01fe03fffff81ffffc,0x27c027c027c027c027c027c027c027c0)
def Fw431 : Sig := (0xfffcffff0001fffe0003fffff81ffffc,0x27c027c027c027c027c027c027c027c0)
def Fw432 : Sig := (0xfffcffffff01fffffe03fffff81ffffc,0x27c027c027c027c027c027c027c027c0)
def Fw433 : Sig := (0xfffcffffff0ffffffe1ffffff8fffffc,0xefcfefcfefcfefcfefcfefcfefcfefcf)
def Fw434 : Sig := (0xfffcfffffffffffffffffffff81ffffc,0xe7c0e7c0e7c0e7c0e7c0e7c0e7c0e7c0)
def Fw435 : Sig := (0xfffeffffffcdffffff9bfffffedffffe,0x27ec27ec27ec27ec27ec27ec27ec27ec)
def Ft0 : Nat → List Entry := fun _ => []

lemma Fv0 : verifiedR configured 11 0 Ft0 := emptyR _ _

def Fg1 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft1 : Nat → List Entry := bucketOf Fg1
lemma Fv1 : verifiedR configured 11 1 Ft1 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv0
  apply checkBuckets
  simp only [Fg1, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def Fg2 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft2 : Nat → List Entry := bucketOf Fg2
lemma Fv2 : verifiedR configured 11 2 Ft2 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv1
  apply checkBuckets
  simp only [Fg2, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def Fg3 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft3 : Nat → List Entry := bucketOf Fg3
lemma Fv3 : verifiedR configured 11 3 Ft3 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv2
  apply checkBuckets
  simp only [Fg3, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def Fg4 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft4 : Nat → List Entry := bucketOf Fg4
lemma Fv4 : verifiedR configured 11 4 Ft4 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv3
  apply checkBuckets
  simp only [Fg4, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def Fg5 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft5 : Nat → List Entry := bucketOf Fg5
lemma Fv5 : verifiedR configured 11 5 Ft5 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv4
  apply checkBuckets
  simp only [Fg5, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def Fg6 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft6 : Nat → List Entry := bucketOf Fg6
lemma Fv6 : verifiedR configured 11 6 Ft6 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv5
  apply checkBuckets
  simp only [Fg6, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true]

def Fp7b2c0 : List Entry := [((1,1),[Fw101,Fw137,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b2c0Ok : Fp7b2c0.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b2 : List Entry := Fp7b2c0
def Fp7b4c0 : List Entry := [((0,0),[Fw65,Fw226,Fw247,Fw282,Fw328,Fw404,Fw423]),
((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw366,Fw404]),
((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw391,Fw423]),
((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw404,Fw423]),
((0,1),[Fw69,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw72,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw101,Fw226,Fw239,Fw265,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw245,Fw282,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b4c0Ok : Fp7b4c0.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b4c1 : List Entry := [((0,1),[Fw101,Fw226,Fw256,Fw262,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw366,Fw388]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw376,Fw423]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw388,Fw420]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw404,Fw423]),
((0,1),[Fw101,Fw226,Fw262,Fw265,Fw282,Fw328,Fw388]),
((0,1),[Fw153,Fw226,Fw239,Fw265,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b4c1Ok : Fp7b4c1.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b4c2 : List Entry := [((1,1),[Fw101,Fw200,Fw239,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b4c2Ok : Fp7b4c2.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b4 : List Entry := Fp7b4c0 ++ Fp7b4c1 ++ Fp7b4c2
def Fp7b6c0 : List Entry := [((0,1),[Fw101,Fw226,Fw262,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw153,Fw226,Fw239,Fw282,Fw328,Fw374,Fw388]),
((1,1),[Fw101,Fw200,Fw239,Fw282,Fw299,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b6c0Ok : Fp7b6c0.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b6 : List Entry := Fp7b6c0
def Fp7b10c0 : List Entry := [((0,0),[Fw65,Fw103,Fw226,Fw239,Fw260,Fw282]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw314,Fw404]),
((0,0),[Fw65,Fw226,Fw254,Fw282,Fw328,Fw404]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw312,Fw398]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw316,Fw404]),
((0,1),[Fw101,Fw226,Fw239,Fw293,Fw312,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw295,Fw328,Fw404]),
((0,1),[Fw101,Fw226,Fw239,Fw297,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b10c0Ok : Fp7b10c0.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b10c1 : List Entry := [((0,1),[Fw101,Fw226,Fw248,Fw282,Fw312,Fw388]),
((0,1),[Fw101,Fw226,Fw252,Fw282,Fw328,Fw404]),
((0,1),[Fw101,Fw226,Fw253,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw319,Fw388]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw397]),
((0,1),[Fw101,Fw226,Fw256,Fw292,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw103,Fw107,Fw239,Fw282]),
((1,0),[Fw65,Fw209,Fw239,Fw282,Fw328,Fw404])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b10c1Ok : Fp7b10c1.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b10c2 : List Entry := [((1,1),[Fw101,Fw210,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw101,Fw212,Fw239,Fw282,Fw328,Fw404]),
((1,1),[Fw101,Fw217,Fw239,Fw282,Fw312,Fw388]),
((1,1),[Fw101,Fw218,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b10c2Ok : Fp7b10c2.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b10 : List Entry := Fp7b10c0 ++ Fp7b10c1 ++ Fp7b10c2
def Fp7b24c0 : List Entry := [((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw404,Fw406]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw388,Fw406])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp7b24c0Ok : Fp7b24c0.all (testRow chart128 configured Ft6 6) = true := by decide +kernel

def Fp7b24 : List Entry := Fp7b24c0
def Fg7 : List (List Entry) := [[], [], Fp7b2, [], Fp7b4, [], Fp7b6, [], [], [], Fp7b10, [], [], [], [], [], [], [], [], [], [], [], [], [], Fp7b24, [], [], [], [], [], [], []]
def Ft7 : Nat → List Entry := bucketOf Fg7
lemma Fv7 : verifiedR configured 11 7 Ft7 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv6
  apply checkBuckets
  simp only [Fg7, Fp7b2, Fp7b4, Fp7b6, Fp7b10, Fp7b24, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, Fp7b2c0Ok, Fp7b4c0Ok, Fp7b4c1Ok, Fp7b4c2Ok, Fp7b6c0Ok, Fp7b10c0Ok, Fp7b10c1Ok, Fp7b10c2Ok, Fp7b24c0Ok]

def Fp8b0c0 : List Entry := [((0,0),[Fw65,Fw226,Fw256,Fw282,Fw299,Fw328,Fw388,Fw423]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b0c0Ok : Fp8b0c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b0 : List Entry := Fp8b0c0
def Fp8b1c0 : List Entry := [((0,0),[Fw65,Fw98,Fw110,Fw226,Fw239,Fw282,Fw328,Fw423]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw363,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw404,Fw432]),
((0,1),[Fw98,Fw101,Fw103,Fw226,Fw239,Fw282,Fw300,Fw328,Fw388]),
((0,1),[Fw101,Fw103,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw367,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw368,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw312,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b1c0Ok : Fp8b1c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b1c1 : List Entry := [((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw340,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388,Fw413])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b1c1Ok : Fp8b1c1.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b1 : List Entry := Fp8b1c0 ++ Fp8b1c1
def Fp8b2c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw417,Fw418]),
((0,0),[Fw65,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388,Fw418]),
((0,1),[Fw101,Fw202,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw205,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw196,Fw197,Fw226,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw137,Fw256,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw137,Fw282,Fw328,Fw388,Fw423]),
((1,1),[Fw98,Fw101,Fw137,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b2c0Ok : Fp8b2c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b2 : List Entry := Fp8b2c0
def Fp8b3c0 : List Entry := [((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw367,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b3c0Ok : Fp8b3c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b3 : List Entry := Fp8b3c0
def Fp8b4c0 : List Entry := [((0,0),[Fw7,Fw65,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw14,Fw65,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw21,Fw65,Fw226,Fw239,Fw282,Fw328,Fw404,Fw423]),
((0,0),[Fw29,Fw65,Fw226,Fw239,Fw282,Fw328,Fw404,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw233,Fw282,Fw328,Fw404,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw265,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw366,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw425])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c0Ok : Fp8b4c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c1 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw391,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw393,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw395,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw398,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw398,Fw425]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404,Fw422]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c1Ok : Fp8b4c1.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw242,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw245,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw247,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw388,Fw425]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw366,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw376,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c2Ok : Fp8b4c2.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c3 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw388,Fw420]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw404,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw262,Fw265,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw109,Fw226,Fw256,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw112,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw265,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c3Ok : Fp8b4c3.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c4 : List Entry := [((0,0),[Fw65,Fw185,Fw226,Fw239,Fw256,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw189,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw247,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw304,Fw328,Fw404]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw310,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw391]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw388,Fw404,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c4Ok : Fp8b4c4.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c5 : List Entry := [((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw404,Fw423]),
((0,1),[Fw14,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw29,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw68,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw69,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw69,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw72,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw72,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c5Ok : Fp8b4c5.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c6 : List Entry := [((0,1),[Fw75,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw78,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw98,Fw101,Fw226,Fw233,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw262,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw366,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw376,Fw423]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw419]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw420])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c6Ok : Fp8b4c6.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c7 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw421]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw422]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw426]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw404,Fw423]),
((0,1),[Fw98,Fw101,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw101,Fw109,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw112,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c7Ok : Fp8b4c7.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c8 : List Entry := [((0,1),[Fw101,Fw148,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw184,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw185,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw245,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw255,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw304,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw376,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c8Ok : Fp8b4c8.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4c9 : List Entry := [((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw404]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((1,0),[Fw65,Fw98,Fw200,Fw239,Fw256,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b4c9Ok : Fp8b4c9.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b4 : List Entry := Fp8b4c0 ++ Fp8b4c1 ++ Fp8b4c2 ++ Fp8b4c3 ++ Fp8b4c4 ++ Fp8b4c5 ++ Fp8b4c6 ++ Fp8b4c7 ++ Fp8b4c8 ++ Fp8b4c9
def Fp8b5c0 : List Entry := [((0,0),[Fw3,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw417]),
((0,0),[Fw65,Fw98,Fw154,Fw226,Fw239,Fw282,Fw328]),
((0,0),[Fw65,Fw103,Fw152,Fw226,Fw239,Fw282,Fw328]),
((0,0),[Fw65,Fw103,Fw226,Fw239,Fw282,Fw312,Fw404]),
((0,0),[Fw65,Fw182,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw398]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw328,Fw334,Fw388]),
((0,1),[Fw15,Fw98,Fw101,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b5c0Ok : Fp8b5c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b5c1 : List Entry := [((0,1),[Fw30,Fw98,Fw101,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw106,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw313,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw328,Fw339,Fw388]),
((1,0),[Fw65,Fw98,Fw103,Fw200,Fw239,Fw282,Fw328]),
((1,0),[Fw65,Fw217,Fw239,Fw282,Fw312,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b5c1Ok : Fp8b5c1.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b5 : List Entry := Fp8b5c0 ++ Fp8b5c1
def Fp8b6c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw262,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw121,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw282,Fw328,Fw374,Fw388]),
((0,1),[Fw78,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw117,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw121,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw148,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b6c0Ok : Fp8b6c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b6c1 : List Entry := [((0,1),[Fw101,Fw185,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw290,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw298,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw304,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw376,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388,Fw404]),
((0,1),[Fw101,Fw226,Fw239,Fw299,Fw328,Fw388,Fw432])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b6c1Ok : Fp8b6c1.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b6c2 : List Entry := [((1,0),[Fw65,Fw98,Fw200,Fw239,Fw282,Fw299,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw138,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b6c2Ok : Fp8b6c2.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b6 : List Entry := Fp8b6c0 ++ Fp8b6c1 ++ Fp8b6c2
def Fp8b7c0 : List Entry := [((0,1),[Fw101,Fw173,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw175,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b7c0Ok : Fp8b7c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b7 : List Entry := Fp8b7c0
def Fp8b9c0 : List Entry := [((0,0),[Fw65,Fw175,Fw226,Fw256,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw175,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b9c0Ok : Fp8b9c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b9 : List Entry := Fp8b9c0
def Fp8b10c0 : List Entry := [((0,0),[Fw7,Fw65,Fw226,Fw239,Fw282,Fw316,Fw388]),
((0,0),[Fw7,Fw65,Fw226,Fw252,Fw282,Fw328,Fw388]),
((0,0),[Fw21,Fw65,Fw226,Fw239,Fw282,Fw328,Fw398]),
((0,0),[Fw24,Fw65,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw64,Fw65,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw259,Fw282]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw262,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw154,Fw226,Fw239,Fw282,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c0Ok : Fp8b10c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c1 : List Entry := [((0,0),[Fw65,Fw98,Fw179,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw234,Fw282,Fw316,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw234,Fw295,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw237,Fw282,Fw328,Fw398]),
((0,0),[Fw65,Fw98,Fw226,Fw237,Fw293,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw238,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw277,Fw316,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw278,Fw328,Fw398])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c1Ok : Fp8b10c1.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw398]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw314,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw315,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw316,Fw376]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw316,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw316,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw322,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw324,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c2Ok : Fp8b10c2.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c3 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw378]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw390]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw394]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw398]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw399]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw402]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw334,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw340,Fw398])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c3Ok : Fp8b10c3.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c4 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw284,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw286,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw288,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw289,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw312,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw328,Fw381]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw328,Fw398])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c4Ok : Fp8b10c4.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c5 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw294,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw295,Fw316,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw295,Fw328,Fw376]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw295,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw295,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw295,Fw338,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw296,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c5Ok : Fp8b10c5.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c6 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw297,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw328,Fw357,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw328,Fw372,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw328,Fw373,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw241,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw243,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw244,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw246,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c6Ok : Fp8b10c6.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c7 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw248,Fw278,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw312,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw381]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw398]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw293,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw251,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c7Ok : Fp8b10c7.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c8 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw252,Fw277,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw252,Fw282,Fw316,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw252,Fw282,Fw328,Fw376]),
((0,0),[Fw65,Fw98,Fw226,Fw252,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw252,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw252,Fw282,Fw338,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw252,Fw295,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw253,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c8Ok : Fp8b10c8.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c9 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw254,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw320,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw396]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw291,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw261,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw262,Fw279,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw262,Fw282,Fw388,Fw413])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c9Ok : Fp8b10c9.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c10 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw262,Fw328,Fw371,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw263,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw264,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw103,Fw152,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw135,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw206,Fw226,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw279,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw282,Fw304,Fw328])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c10Ok : Fp8b10c10.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c11 : List Entry := [((0,0),[Fw65,Fw152,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw282,Fw388,Fw413]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw328,Fw371,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw260,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw316,Fw388,Fw404]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw328,Fw378,Fw388]),
((0,0),[Fw65,Fw226,Fw252,Fw282,Fw328,Fw388,Fw404])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c11Ok : Fp8b10c11.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c12 : List Entry := [((0,1),[Fw9,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw11,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw14,Fw78,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw14,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw14,Fw101,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,1),[Fw15,Fw101,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,1),[Fw16,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw17,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c12Ok : Fp8b10c12.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c13 : List Entry := [((0,1),[Fw23,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw24,Fw76,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw24,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw25,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw26,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw29,Fw69,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw29,Fw72,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw29,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c13Ok : Fp8b10c13.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c14 : List Entry := [((0,1),[Fw29,Fw101,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw30,Fw101,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw31,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw32,Fw79,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw32,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw33,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw34,Fw80,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw34,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c14Ok : Fp8b10c14.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c15 : List Entry := [((0,1),[Fw35,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw36,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw38,Fw101,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw40,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw42,Fw101,Fw226,Fw239,Fw282,Fw312,Fw388]),
((0,1),[Fw44,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw46,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw47,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c15Ok : Fp8b10c15.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c16 : List Entry := [((0,1),[Fw52,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw54,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw56,Fw101,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,1),[Fw58,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw59,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw61,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw63,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw66,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c16Ok : Fp8b10c16.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c17 : List Entry := [((0,1),[Fw67,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw68,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw69,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw70,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw71,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw72,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw73,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw74,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c17Ok : Fp8b10c17.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c18 : List Entry := [((0,1),[Fw75,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw76,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw77,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw78,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw79,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw80,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw81,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw83,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c18Ok : Fp8b10c18.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c19 : List Entry := [((0,1),[Fw84,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw85,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw86,Fw98,Fw226,Fw239,Fw282,Fw328,Fw398]),
((0,1),[Fw86,Fw98,Fw226,Fw239,Fw293,Fw328,Fw388]),
((0,1),[Fw86,Fw98,Fw226,Fw248,Fw282,Fw328,Fw388]),
((0,1),[Fw87,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw88,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw89,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c19Ok : Fp8b10c19.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c20 : List Entry := [((0,1),[Fw91,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw92,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw93,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw94,Fw98,Fw226,Fw239,Fw282,Fw316,Fw388]),
((0,1),[Fw94,Fw98,Fw226,Fw239,Fw295,Fw328,Fw388]),
((0,1),[Fw94,Fw98,Fw226,Fw252,Fw282,Fw328,Fw388]),
((0,1),[Fw95,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw96,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c20Ok : Fp8b10c20.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c21 : List Entry := [((0,1),[Fw97,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw120,Fw226,Fw239,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw172,Fw226,Fw239,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw180,Fw226,Fw239,Fw282,Fw388]),
((0,1),[Fw98,Fw101,Fw192,Fw226,Fw239,Fw282,Fw328]),
((0,1),[Fw98,Fw101,Fw206,Fw226,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw234,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw235,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c21Ok : Fp8b10c21.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c22 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw236,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw237,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw277,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw278,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw279,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw280,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw281,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw316,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c22Ok : Fp8b10c22.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c23 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw317,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw318,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw319,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw320,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw377,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw379]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw380]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw381])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c23Ok : Fp8b10c23.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c24 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw383]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw384]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw397]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw396]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw397]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw398]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw400])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c24Ok : Fp8b10c24.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c25 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw401]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw332,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw333,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw336,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw337,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw338,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw343,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw361,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c25Ok : Fp8b10c25.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c26 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw291,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw292,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw293,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw295,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw328,Fw356,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw328,Fw371,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw328,Fw388,Fw429]),
((0,1),[Fw98,Fw101,Fw226,Fw248,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c26Ok : Fp8b10c26.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c27 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw249,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw250,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw252,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw151,Fw226,Fw239,Fw328,Fw371,Fw388]),
((0,1),[Fw98,Fw151,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw153,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw158,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c27Ok : Fp8b10c27.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c28 : List Entry := [((0,1),[Fw98,Fw165,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw167,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw226,Fw231,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw99,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw100,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw152,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw230,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw270,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c28Ok : Fp8b10c28.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c29 : List Entry := [((0,1),[Fw101,Fw226,Fw239,Fw282,Fw328,Fw377,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw403]),
((0,1),[Fw151,Fw152,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw152,Fw153,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw226,Fw230,Fw231,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw7,Fw65,Fw212,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw21,Fw65,Fw217,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw24,Fw65,Fw200,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c29Ok : Fp8b10c29.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c30 : List Entry := [((1,0),[Fw65,Fw98,Fw103,Fw200,Fw239,Fw282,Fw388]),
((1,0),[Fw65,Fw98,Fw107,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw132,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw198,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw199,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw200,Fw206,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw200,Fw239,Fw279,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw200,Fw239,Fw282,Fw304,Fw328])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c30Ok : Fp8b10c30.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c31 : List Entry := [((1,0),[Fw65,Fw98,Fw200,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw200,Fw239,Fw282,Fw388,Fw413]),
((1,0),[Fw65,Fw98,Fw200,Fw239,Fw328,Fw371,Fw388]),
((1,0),[Fw65,Fw98,Fw200,Fw262,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw201,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw208,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw209,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw210,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c31Ok : Fp8b10c31.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c32 : List Entry := [((1,0),[Fw65,Fw98,Fw211,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw234,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw277,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw282,Fw316,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw282,Fw328,Fw376]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw282,Fw328,Fw404]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw282,Fw338,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c32Ok : Fp8b10c32.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c33 : List Entry := [((1,0),[Fw65,Fw98,Fw212,Fw239,Fw295,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw252,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw213,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw216,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw237,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw278,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw312,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw328,Fw381])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c33Ok : Fp8b10c33.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c34 : List Entry := [((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw328,Fw398]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw340,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw293,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw248,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw219,Fw256,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw220,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw221,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c34Ok : Fp8b10c34.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c35 : List Entry := [((1,0),[Fw65,Fw98,Fw222,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw223,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw224,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw225,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw152,Fw200,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw212,Fw239,Fw282,Fw328,Fw388,Fw404]),
((1,1),[Fw86,Fw98,Fw217,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw94,Fw98,Fw212,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c35Ok : Fp8b10c35.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c36 : List Entry := [((1,1),[Fw98,Fw101,Fw133,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw200,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw212,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw214,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw215,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw217,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw218,Fw239,Fw282,Fw328,Fw388]),
((1,1),[Fw98,Fw101,Fw219,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c36Ok : Fp8b10c36.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10c37 : List Entry := [((1,1),[Fw98,Fw151,Fw200,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b10c37Ok : Fp8b10c37.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b10 : List Entry := Fp8b10c0 ++ Fp8b10c1 ++ Fp8b10c2 ++ Fp8b10c3 ++ Fp8b10c4 ++ Fp8b10c5 ++ Fp8b10c6 ++ Fp8b10c7 ++ Fp8b10c8 ++ Fp8b10c9 ++ Fp8b10c10 ++ Fp8b10c11 ++ Fp8b10c12 ++ Fp8b10c13 ++ Fp8b10c14 ++ Fp8b10c15 ++ Fp8b10c16 ++ Fp8b10c17 ++ Fp8b10c18 ++ Fp8b10c19 ++ Fp8b10c20 ++ Fp8b10c21 ++ Fp8b10c22 ++ Fp8b10c23 ++ Fp8b10c24 ++ Fp8b10c25 ++ Fp8b10c26 ++ Fp8b10c27 ++ Fp8b10c28 ++ Fp8b10c29 ++ Fp8b10c30 ++ Fp8b10c31 ++ Fp8b10c32 ++ Fp8b10c33 ++ Fp8b10c34 ++ Fp8b10c35 ++ Fp8b10c36 ++ Fp8b10c37
def Fp8b12c0 : List Entry := [((0,1),[Fw101,Fw141,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b12c0Ok : Fp8b12c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b12 : List Entry := Fp8b12c0
def Fp8b13c0 : List Entry := [((0,1),[Fw101,Fw175,Fw226,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b13c0Ok : Fp8b13c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b13 : List Entry := Fp8b13c0
def Fp8b17c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw417]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw328,Fw417]),
((0,0),[Fw65,Fw103,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw196,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,1),[Fw98,Fw103,Fw195,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw195,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b17c0Ok : Fp8b17c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b17 : List Entry := Fp8b17c0
def Fp8b20c0 : List Entry := [((0,0),[Fw65,Fw226,Fw256,Fw282,Fw328,Fw358,Fw388,Fw404]),
((0,0),[Fw65,Fw226,Fw256,Fw299,Fw328,Fw358,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw328,Fw359,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw299,Fw328,Fw358,Fw388]),
((0,1),[Fw101,Fw226,Fw256,Fw282,Fw328,Fw358,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b20c0Ok : Fp8b20c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b20 : List Entry := Fp8b20c0
def Fp8b22c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw418]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404,Fw417]),
((0,0),[Fw65,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw417]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw417]),
((0,1),[Fw98,Fw195,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,1),[Fw98,Fw197,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b22c0Ok : Fp8b22c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b22c1 : List Entry := [((0,1),[Fw101,Fw226,Fw239,Fw271,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw274,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b22c1Ok : Fp8b22c1.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b22 : List Entry := Fp8b22c0 ++ Fp8b22c1
def Fp8b24c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404,Fw406]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw388,Fw406]),
((0,0),[Fw65,Fw142,Fw226,Fw256,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw145,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw406]),
((0,1),[Fw101,Fw142,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw143,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw145,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b24c0Ok : Fp8b24c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b24 : List Entry := Fp8b24c0
def Fp8b25c0 : List Entry := [((0,1),[Fw101,Fw125,Fw226,Fw239,Fw299,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b25c0Ok : Fp8b25c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b25 : List Entry := Fp8b25c0
def Fp8b26c0 : List Entry := [((0,1),[Fw98,Fw101,Fw194,Fw226,Fw239,Fw328,Fw388]),
((0,1),[Fw101,Fw115,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw169,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,1),[Fw101,Fw170,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw171,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b26c0Ok : Fp8b26c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b26 : List Entry := Fp8b26c0
def Fp8b27c0 : List Entry := [((1,0),[Fw18,Fw65,Fw98,Fw200,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw130,Fw212,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw131,Fw217,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b27c0Ok : Fp8b27c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b27 : List Entry := Fp8b27c0
def Fp8b28c0 : List Entry := [((0,1),[Fw98,Fw101,Fw144,Fw226,Fw239,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b28c0Ok : Fp8b28c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b28 : List Entry := Fp8b28c0
def Fp8b29c0 : List Entry := [((0,0),[Fw65,Fw98,Fw118,Fw175,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw282,Fw350,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw181,Fw226,Fw282,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b29c0Ok : Fp8b29c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b29 : List Entry := Fp8b29c0
def Fp8b30c0 : List Entry := [((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw404,Fw423]),
((0,1),[Fw98,Fw101,Fw183,Fw226,Fw239,Fw282,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw426])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b30c0Ok : Fp8b30c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b30 : List Entry := Fp8b30c0
def Fp8b31c0 : List Entry := [((0,0),[Fw65,Fw103,Fw226,Fw239,Fw256,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw404,Fw423]),
((0,1),[Fw98,Fw101,Fw103,Fw226,Fw239,Fw257,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw103,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw312,Fw328,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw340,Fw388]),
((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw413])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp8b31c0Ok : Fp8b31c0.all (testRow chart128 configured Ft7 7) = true := by decide +kernel

def Fp8b31 : List Entry := Fp8b31c0
def Fg8 : List (List Entry) := [Fp8b0, Fp8b1, Fp8b2, Fp8b3, Fp8b4, Fp8b5, Fp8b6, Fp8b7, [], Fp8b9, Fp8b10, [], Fp8b12, Fp8b13, [], [], [], Fp8b17, [], [], Fp8b20, [], Fp8b22, [], Fp8b24, Fp8b25, Fp8b26, Fp8b27, Fp8b28, Fp8b29, Fp8b30, Fp8b31]
def Ft8 : Nat → List Entry := bucketOf Fg8
lemma Fv8 : verifiedR configured 11 8 Ft8 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv7
  apply checkBuckets
  simp only [Fg8, Fp8b0, Fp8b1, Fp8b2, Fp8b3, Fp8b4, Fp8b5, Fp8b6, Fp8b7, Fp8b9, Fp8b10, Fp8b12, Fp8b13, Fp8b17, Fp8b20, Fp8b22, Fp8b24, Fp8b25, Fp8b26, Fp8b27, Fp8b28, Fp8b29, Fp8b30, Fp8b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, Fp8b0c0Ok, Fp8b1c0Ok, Fp8b1c1Ok, Fp8b2c0Ok, Fp8b3c0Ok, Fp8b4c0Ok, Fp8b4c1Ok, Fp8b4c2Ok, Fp8b4c3Ok, Fp8b4c4Ok, Fp8b4c5Ok, Fp8b4c6Ok, Fp8b4c7Ok, Fp8b4c8Ok, Fp8b4c9Ok, Fp8b5c0Ok, Fp8b5c1Ok, Fp8b6c0Ok, Fp8b6c1Ok, Fp8b6c2Ok, Fp8b7c0Ok, Fp8b9c0Ok, Fp8b10c0Ok, Fp8b10c1Ok, Fp8b10c2Ok, Fp8b10c3Ok, Fp8b10c4Ok, Fp8b10c5Ok, Fp8b10c6Ok, Fp8b10c7Ok, Fp8b10c8Ok, Fp8b10c9Ok, Fp8b10c10Ok, Fp8b10c11Ok, Fp8b10c12Ok, Fp8b10c13Ok, Fp8b10c14Ok, Fp8b10c15Ok, Fp8b10c16Ok, Fp8b10c17Ok, Fp8b10c18Ok, Fp8b10c19Ok, Fp8b10c20Ok, Fp8b10c21Ok, Fp8b10c22Ok, Fp8b10c23Ok, Fp8b10c24Ok, Fp8b10c25Ok, Fp8b10c26Ok, Fp8b10c27Ok, Fp8b10c28Ok, Fp8b10c29Ok, Fp8b10c30Ok, Fp8b10c31Ok, Fp8b10c32Ok, Fp8b10c33Ok, Fp8b10c34Ok, Fp8b10c35Ok, Fp8b10c36Ok, Fp8b10c37Ok, Fp8b12c0Ok, Fp8b13c0Ok, Fp8b17c0Ok, Fp8b20c0Ok, Fp8b22c0Ok, Fp8b22c1Ok, Fp8b24c0Ok, Fp8b25c0Ok, Fp8b26c0Ok, Fp8b27c0Ok, Fp8b28c0Ok, Fp8b29c0Ok, Fp8b30c0Ok, Fp8b31c0Ok]

def Fp9b0c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw423,Fw432]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw340,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b0c0Ok : Fp9b0c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b0 : List Entry := Fp9b0c0
def Fp9b1c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw117,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw276,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw117,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw175,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw368,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b1c0Ok : Fp9b1c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b1c1 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw276,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw340,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw367,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw413,Fw432])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b1c1Ok : Fp9b1c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b1c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423,Fw424])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b1c2Ok : Fp9b1c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b1 : List Entry := Fp9b1c0 ++ Fp9b1c1 ++ Fp9b1c2
def Fp9b2c0 : List Entry := [((0,0),[Fw65,Fw98,Fw202,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw202,Fw226,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw204,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw205,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw326,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw411]),
((0,1),[Fw98,Fw101,Fw202,Fw226,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw137,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b2c0Ok : Fp9b2c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b2 : List Entry := Fp9b2c0
def Fp9b3c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw367,Fw388,Fw432])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b3c0Ok : Fp9b3c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b3 : List Entry := Fp9b3c0
def Fp9b4c0 : List Entry := [((0,0),[Fw5,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw7,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw7,Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw14,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw14,Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw21,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw29,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c0Ok : Fp9b4c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4c1 : List Entry := [((0,0),[Fw65,Fw98,Fw108,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw109,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw109,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw111,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw112,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw159,Fw226,Fw239,Fw282,Fw328,Fw423]),
((0,0),[Fw65,Fw98,Fw184,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c1Ok : Fp9b4c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4c2 : List Entry := [((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw233,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw233,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw242,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw245,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw247,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw248,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw252,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c2Ok : Fp9b4c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4c3 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw304,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw376,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw267,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw366,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw376,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c3Ok : Fp9b4c3.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4c4 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404,Fw426]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw419]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw420]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw422]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw426]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c4Ok : Fp9b4c4.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4c5 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw404]),
((0,1),[Fw98,Fw101,Fw109,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw232,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw233,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw257,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c5Ok : Fp9b4c5.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4c6 : List Entry := [((0,1),[Fw101,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b4c6Ok : Fp9b4c6.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b4 : List Entry := Fp9b4c0 ++ Fp9b4c1 ++ Fp9b4c2 ++ Fp9b4c3 ++ Fp9b4c4 ++ Fp9b4c5 ++ Fp9b4c6
def Fp9b5c0 : List Entry := [((0,0),[Fw7,Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw21,Fw65,Fw226,Fw239,Fw282,Fw328,Fw340,Fw388]),
((0,0),[Fw42,Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw102,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw148,Fw226,Fw239,Fw282,Fw328]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw312,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw376]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c0Ok : Fp9b5c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5c1 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw104,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw105,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw106,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw129,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw180,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw203,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c1Ok : Fp9b5c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5c2 : List Entry := [((0,0),[Fw65,Fw98,Fw207,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw272,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw304,Fw328,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw316,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw318,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw320,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c2Ok : Fp9b5c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5c3 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw321,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw323,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw325,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw329,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw330,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw331,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw332,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw335,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c3Ok : Fp9b5c3.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5c4 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw336,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw338,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw343,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw355,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw361,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw407]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw408])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c4Ok : Fp9b5c4.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5c5 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw409]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw410]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw414]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw340,Fw388,Fw413]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388,Fw404]),
((0,1),[Fw98,Fw101,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw311,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c5Ok : Fp9b5c5.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5c6 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw340,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw341,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw413])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b5c6Ok : Fp9b5c6.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b5 : List Entry := Fp9b5c0 ++ Fp9b5c1 ++ Fp9b5c2 ++ Fp9b5c3 ++ Fp9b5c4 ++ Fp9b5c5 ++ Fp9b5c6
def Fp9b6c0 : List Entry := [((0,0),[Fw29,Fw65,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw116,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw117,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw117,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw119,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw121,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b6c0Ok : Fp9b6c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b6c1 : List Entry := [((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw282,Fw328,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw276,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw276,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw285,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw287,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw290,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw293,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw295,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b6c1Ok : Fp9b6c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b6c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw304,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw376,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw349,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw353,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw376,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404,Fw432])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b6c2Ok : Fp9b6c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b6c3 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404,Fw434]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw428]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw430]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw431]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw434]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw299,Fw328,Fw388,Fw432])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b6c3Ok : Fp9b6c3.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b6c4 : List Entry := [((0,1),[Fw98,Fw101,Fw117,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw275,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw276,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw300,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw432]),
((0,1),[Fw101,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw138,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b6c4Ok : Fp9b6c4.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b6 : List Entry := Fp9b6c0 ++ Fp9b6c1 ++ Fp9b6c2 ++ Fp9b6c3 ++ Fp9b6c4
def Fp9b7c0 : List Entry := [((0,0),[Fw2,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw110,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw173,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw240,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw258,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b7c0Ok : Fp9b7c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b7c1 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw344,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw362,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw363,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw364,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw365,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw368,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b7c1Ok : Fp9b7c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b7c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw424]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw340,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw367,Fw388,Fw413]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw367,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b7c2Ok : Fp9b7c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b7 : List Entry := Fp9b7c0 ++ Fp9b7c1 ++ Fp9b7c2
def Fp9b8c0 : List Entry := [((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw328,Fw350,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b8c0Ok : Fp9b8c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b8 : List Entry := Fp9b8c0
def Fp9b9c0 : List Entry := [((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw302,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b9c0Ok : Fp9b9c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b9 : List Entry := Fp9b9c0
def Fp9b10c0 : List Entry := [((0,0),[Fw1,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw4,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw5,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw6,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw7,Fw21,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw7,Fw29,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw7,Fw56,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw7,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw376])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c0Ok : Fp9b10c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c1 : List Entry := [((0,0),[Fw7,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw7,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,0),[Fw7,Fw65,Fw226,Fw239,Fw282,Fw328,Fw376,Fw388]),
((0,0),[Fw10,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw11,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw12,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw13,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw14,Fw29,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c1Ok : Fp9b10c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c2 : List Entry := [((0,0),[Fw14,Fw65,Fw98,Fw226,Fw239,Fw276,Fw328,Fw388]),
((0,0),[Fw14,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw14,Fw65,Fw98,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,0),[Fw17,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw19,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw20,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw21,Fw42,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw21,Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c2Ok : Fp9b10c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c3 : List Entry := [((0,0),[Fw21,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw21,Fw65,Fw98,Fw226,Fw239,Fw282,Fw340,Fw388]),
((0,0),[Fw21,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw24,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw24,Fw65,Fw148,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw24,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw26,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw27,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c3Ok : Fp9b10c3.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c4 : List Entry := [((0,0),[Fw28,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw29,Fw65,Fw98,Fw226,Fw233,Fw282,Fw328,Fw388]),
((0,0),[Fw29,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw29,Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw29,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw32,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw32,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw34,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c4Ok : Fp9b10c4.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c5 : List Entry := [((0,0),[Fw34,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw36,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw37,Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw39,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw40,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw41,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw237,Fw282,Fw328,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw278,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c5Ok : Fp9b10c5.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c6 : List Entry := [((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw381]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw398]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw340,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw293,Fw328,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw388]),
((0,0),[Fw45,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c6Ok : Fp9b10c6.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c7 : List Entry := [((0,0),[Fw46,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw47,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw48,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw51,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw53,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw54,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw55,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw234,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c7Ok : Fp9b10c7.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c8 : List Entry := [((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw277,Fw328,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw282,Fw316,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw376]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw282,Fw338,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw295,Fw328,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw252,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c8Ok : Fp9b10c8.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c9 : List Entry := [((0,0),[Fw56,Fw65,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw59,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw60,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw61,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw62,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw63,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw64,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw148,Fw226,Fw239,Fw282,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c9Ok : Fp9b10c9.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c10 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw304,Fw388]),
((0,0),[Fw65,Fw98,Fw109,Fw185,Fw226,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw124,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw134,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw136,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw147,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw148,Fw206,Fw226,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw279,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c10Ok : Fp9b10c10.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c11 : List Entry := [((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw282,Fw304,Fw328]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw282,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw328,Fw371,Fw388]),
((0,0),[Fw65,Fw98,Fw148,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw149,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw150,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw152,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c11Ok : Fp9b10c11.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c12 : List Entry := [((0,0),[Fw65,Fw98,Fw157,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw159,Fw185,Fw226,Fw239,Fw282,Fw328]),
((0,0),[Fw65,Fw98,Fw159,Fw226,Fw239,Fw282,Fw328,Fw376]),
((0,0),[Fw65,Fw98,Fw159,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw159,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw159,Fw226,Fw239,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw161,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw162,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c12Ok : Fp9b10c12.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c13 : List Entry := [((0,0),[Fw65,Fw98,Fw163,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw166,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw172,Fw226,Fw239,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw174,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw180,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw184,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw282,Fw328,Fw376]),
((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c13Ok : Fp9b10c13.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c14 : List Entry := [((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw282,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw185,Fw226,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw187,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw188,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw189,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw191,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw192,Fw226,Fw239,Fw282,Fw328]),
((0,0),[Fw65,Fw98,Fw192,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c14Ok : Fp9b10c14.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c15 : List Entry := [((0,0),[Fw65,Fw98,Fw206,Fw226,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw228,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw230,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw234,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw236,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw237,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw259,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw266,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c15Ok : Fp9b10c15.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c16 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw268,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw269,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw270,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw277,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw278,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw279,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw281,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw303,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c16Ok : Fp9b10c16.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c17 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw304,Fw328,Fw376]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw304,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw304,Fw328,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw304,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw307,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw308,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw309,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw310,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c17Ok : Fp9b10c17.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c18 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw316,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw318,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw320,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw352,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw354,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw360,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw370,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw376,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c18Ok : Fp9b10c18.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c19 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw380]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw380,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw381]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw381,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw382,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw384]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw384,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw385,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c19Ok : Fp9b10c19.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c20 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw386,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw387,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw391]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw393]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw395]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw396]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw398]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw400])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c20Ok : Fp9b10c20.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c21 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw396]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw398]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw400]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw332,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw336,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw338,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw343,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c21Ok : Fp9b10c21.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c22 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw361,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw291,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw293,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw295,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw328,Fw356,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw328,Fw371,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw248,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw249,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c22Ok : Fp9b10c22.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c23 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw252,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw262,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw148,Fw152,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw152,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw230,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw226,Fw239,Fw282,Fw328,Fw376,Fw388,Fw404]),
((0,1),[Fw7,Fw69,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw7,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c23Ok : Fp9b10c23.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c24 : List Entry := [((0,1),[Fw8,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw14,Fw72,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw14,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw14,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw15,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw21,Fw75,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw21,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw22,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c24Ok : Fp9b10c24.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c25 : List Entry := [((0,1),[Fw29,Fw78,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw29,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw29,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw30,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw37,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw38,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw42,Fw86,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw42,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c25Ok : Fp9b10c25.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c26 : List Entry := [((0,1),[Fw43,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw49,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw50,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw56,Fw94,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw56,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw57,Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw69,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw72,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c26Ok : Fp9b10c26.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c27 : List Entry := [((0,1),[Fw75,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw78,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw82,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw86,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw90,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw94,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw148,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw159,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c27Ok : Fp9b10c27.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c28 : List Entry := [((0,1),[Fw98,Fw101,Fw185,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw227,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw268,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw304,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw375,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw376,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388,Fw405])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c28Ok : Fp9b10c28.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c29 : List Entry := [((0,1),[Fw98,Fw148,Fw151,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw151,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw159,Fw164,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw164,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw226,Fw229,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw42,Fw65,Fw98,Fw217,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw56,Fw65,Fw98,Fw212,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw133,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c29Ok : Fp9b10c29.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10c30 : List Entry := [((1,0),[Fw65,Fw98,Fw148,Fw200,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw200,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw212,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw215,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw217,Fw239,Fw282,Fw328,Fw388]),
((1,0),[Fw65,Fw98,Fw219,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b10c30Ok : Fp9b10c30.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b10 : List Entry := Fp9b10c0 ++ Fp9b10c1 ++ Fp9b10c2 ++ Fp9b10c3 ++ Fp9b10c4 ++ Fp9b10c5 ++ Fp9b10c6 ++ Fp9b10c7 ++ Fp9b10c8 ++ Fp9b10c9 ++ Fp9b10c10 ++ Fp9b10c11 ++ Fp9b10c12 ++ Fp9b10c13 ++ Fp9b10c14 ++ Fp9b10c15 ++ Fp9b10c16 ++ Fp9b10c17 ++ Fp9b10c18 ++ Fp9b10c19 ++ Fp9b10c20 ++ Fp9b10c21 ++ Fp9b10c22 ++ Fp9b10c23 ++ Fp9b10c24 ++ Fp9b10c25 ++ Fp9b10c26 ++ Fp9b10c27 ++ Fp9b10c28 ++ Fp9b10c29 ++ Fp9b10c30
def Fp9b12c0 : List Entry := [((0,0),[Fw65,Fw98,Fw140,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw141,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw155,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw416]),
((0,1),[Fw98,Fw101,Fw139,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b12c0Ok : Fp9b12c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b12 : List Entry := Fp9b12c0
def Fp9b13c0 : List Entry := [((0,0),[Fw2,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw175,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw109,Fw175,Fw226,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw122,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw173,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw233,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw312,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b13c0Ok : Fp9b13c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b13c1 : List Entry := [((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw175,Fw226,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw176,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw177,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw178,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw186,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b13c1Ok : Fp9b13c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b13c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw306,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw392]),
((0,1),[Fw98,Fw101,Fw175,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b13c2Ok : Fp9b13c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b13 : List Entry := Fp9b13c0 ++ Fp9b13c1 ++ Fp9b13c2
def Fp9b15c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw358,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw328,Fw358,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw350,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b15c0Ok : Fp9b15c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b15 : List Entry := Fp9b15c0
def Fp9b16c0 : List Entry := [((0,0),[Fw65,Fw98,Fw175,Fw226,Fw282,Fw328,Fw367,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b16c0Ok : Fp9b16c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b16 : List Entry := Fp9b16c0
def Fp9b17c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw193,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw193,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b17c0Ok : Fp9b17c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b17 : List Entry := Fp9b17c0
def Fp9b19c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw142,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw142,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b19c0Ok : Fp9b19c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b19 : List Entry := Fp9b19c0
def Fp9b20c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw358,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw359,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw435]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw299,Fw328,Fw358,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw328,Fw358,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw256,Fw282,Fw328,Fw358,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw358,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b20c0Ok : Fp9b20c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b20 : List Entry := Fp9b20c0
def Fp9b21c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw169,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw118,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw139,Fw175,Fw226,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw169,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw283,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw350,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw342,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw345,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b21c0Ok : Fp9b21c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b21c1 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw346,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw347,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw348,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw350,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw351,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw433]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw340,Fw350,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw350,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b21c1Ok : Fp9b21c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b21 : List Entry := Fp9b21c0 ++ Fp9b21c1
def Fp9b22c0 : List Entry := [((0,0),[Fw65,Fw98,Fw193,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw271,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw271,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw273,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw274,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw327,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw412])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b22c0Ok : Fp9b22c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b22c1 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw417]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw417]),
((0,0),[Fw65,Fw196,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw193,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw226,Fw239,Fw271,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw195,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b22c1Ok : Fp9b22c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b22 : List Entry := Fp9b22c0 ++ Fp9b22c1
def Fp9b23c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw369,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw350,Fw367,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b23c0Ok : Fp9b23c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b23 : List Entry := Fp9b23c0
def Fp9b24c0 : List Entry := [((0,0),[Fw65,Fw98,Fw142,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw142,Fw226,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw143,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw145,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw168,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw406]),
((0,1),[Fw98,Fw101,Fw142,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b24c0Ok : Fp9b24c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b24 : List Entry := Fp9b24c0
def Fp9b25c0 : List Entry := [((0,0),[Fw0,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw117,Fw125,Fw226,Fw239,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw123,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw276,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw282,Fw312,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw282,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw299,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b25c0Ok : Fp9b25c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b25c1 : List Entry := [((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw126,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw127,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw128,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw160,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw183,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw301,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw305,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b25c1Ok : Fp9b25c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b25c2 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw389]),
((0,1),[Fw98,Fw101,Fw125,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b25c2Ok : Fp9b25c2.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b25 : List Entry := Fp9b25c0 ++ Fp9b25c1 ++ Fp9b25c2
def Fp9b26c0 : List Entry := [((0,0),[Fw65,Fw98,Fw114,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw115,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw156,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw169,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404]),
((0,0),[Fw65,Fw98,Fw169,Fw226,Fw239,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw169,Fw226,Fw239,Fw328,Fw388,Fw432]),
((0,0),[Fw65,Fw98,Fw170,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw171,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b26c0Ok : Fp9b26c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b26c1 : List Entry := [((0,0),[Fw65,Fw98,Fw190,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw415]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw427]),
((0,1),[Fw98,Fw101,Fw113,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,1),[Fw98,Fw101,Fw169,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b26c1Ok : Fp9b26c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b26 : List Entry := Fp9b26c0 ++ Fp9b26c1
def Fp9b27c0 : List Entry := [((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw282,Fw367,Fw388]),
((0,0),[Fw65,Fw98,Fw146,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b27c0Ok : Fp9b27c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b27 : List Entry := Fp9b27c0
def Fp9b29c0 : List Entry := [((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw350,Fw388]),
((0,0),[Fw65,Fw98,Fw181,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b29c0Ok : Fp9b29c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b29 : List Entry := Fp9b29c0
def Fp9b30c0 : List Entry := [((0,0),[Fw65,Fw98,Fw183,Fw226,Fw239,Fw282,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw426]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423,Fw426])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b30c0Ok : Fp9b30c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b30 : List Entry := Fp9b30c0
def Fp9b31c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw109,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw233,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw109,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw233,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw340,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b31c0Ok : Fp9b31c0.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b31c1 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388,Fw413]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw340,Fw388,Fw423]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw413,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp9b31c1Ok : Fp9b31c1.all (testRow chart128 configured Ft8 8) = true := by decide +kernel

def Fp9b31 : List Entry := Fp9b31c0 ++ Fp9b31c1
def Fg9 : List (List Entry) := [Fp9b0, Fp9b1, Fp9b2, Fp9b3, Fp9b4, Fp9b5, Fp9b6, Fp9b7, Fp9b8, Fp9b9, Fp9b10, [], Fp9b12, Fp9b13, [], Fp9b15, Fp9b16, Fp9b17, [], Fp9b19, Fp9b20, Fp9b21, Fp9b22, Fp9b23, Fp9b24, Fp9b25, Fp9b26, Fp9b27, [], Fp9b29, Fp9b30, Fp9b31]
def Ft9 : Nat → List Entry := bucketOf Fg9
lemma Fv9 : verifiedR configured 11 9 Ft9 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv8
  apply checkBuckets
  simp only [Fg9, Fp9b0, Fp9b1, Fp9b2, Fp9b3, Fp9b4, Fp9b5, Fp9b6, Fp9b7, Fp9b8, Fp9b9, Fp9b10, Fp9b12, Fp9b13, Fp9b15, Fp9b16, Fp9b17, Fp9b19, Fp9b20, Fp9b21, Fp9b22, Fp9b23, Fp9b24, Fp9b25, Fp9b26, Fp9b27, Fp9b29, Fp9b30, Fp9b31, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, Fp9b0c0Ok, Fp9b1c0Ok, Fp9b1c1Ok, Fp9b1c2Ok, Fp9b2c0Ok, Fp9b3c0Ok, Fp9b4c0Ok, Fp9b4c1Ok, Fp9b4c2Ok, Fp9b4c3Ok, Fp9b4c4Ok, Fp9b4c5Ok, Fp9b4c6Ok, Fp9b5c0Ok, Fp9b5c1Ok, Fp9b5c2Ok, Fp9b5c3Ok, Fp9b5c4Ok, Fp9b5c5Ok, Fp9b5c6Ok, Fp9b6c0Ok, Fp9b6c1Ok, Fp9b6c2Ok, Fp9b6c3Ok, Fp9b6c4Ok, Fp9b7c0Ok, Fp9b7c1Ok, Fp9b7c2Ok, Fp9b8c0Ok, Fp9b9c0Ok, Fp9b10c0Ok, Fp9b10c1Ok, Fp9b10c2Ok, Fp9b10c3Ok, Fp9b10c4Ok, Fp9b10c5Ok, Fp9b10c6Ok, Fp9b10c7Ok, Fp9b10c8Ok, Fp9b10c9Ok, Fp9b10c10Ok, Fp9b10c11Ok, Fp9b10c12Ok, Fp9b10c13Ok, Fp9b10c14Ok, Fp9b10c15Ok, Fp9b10c16Ok, Fp9b10c17Ok, Fp9b10c18Ok, Fp9b10c19Ok, Fp9b10c20Ok, Fp9b10c21Ok, Fp9b10c22Ok, Fp9b10c23Ok, Fp9b10c24Ok, Fp9b10c25Ok, Fp9b10c26Ok, Fp9b10c27Ok, Fp9b10c28Ok, Fp9b10c29Ok, Fp9b10c30Ok, Fp9b12c0Ok, Fp9b13c0Ok, Fp9b13c1Ok, Fp9b13c2Ok, Fp9b15c0Ok, Fp9b16c0Ok, Fp9b17c0Ok, Fp9b19c0Ok, Fp9b20c0Ok, Fp9b21c0Ok, Fp9b21c1Ok, Fp9b22c0Ok, Fp9b22c1Ok, Fp9b23c0Ok, Fp9b24c0Ok, Fp9b25c0Ok, Fp9b25c1Ok, Fp9b25c2Ok, Fp9b26c0Ok, Fp9b26c1Ok, Fp9b27c0Ok, Fp9b29c0Ok, Fp9b30c0Ok, Fp9b31c0Ok, Fp9b31c1Ok]

def Fp10b2c0 : List Entry := [((0,0),[Fw65,Fw98,Fw202,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b2c0Ok : Fp10b2c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b2 : List Entry := Fp10b2c0
def Fp10b4c0 : List Entry := [((0,0),[Fw65,Fw98,Fw109,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw233,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw256,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw423])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b4c0Ok : Fp10b4c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b4 : List Entry := Fp10b4c0
def Fp10b5c0 : List Entry := [((0,0),[Fw65,Fw98,Fw103,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw312,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw340,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw413])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b5c0Ok : Fp10b5c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b5 : List Entry := Fp10b5c0
def Fp10b6c0 : List Entry := [((0,0),[Fw65,Fw98,Fw117,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw276,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw299,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw432])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b6c0Ok : Fp10b6c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b6 : List Entry := Fp10b6c0
def Fp10b7c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw367,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b7c0Ok : Fp10b7c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b7 : List Entry := Fp10b7c0
def Fp10b10c0 : List Entry := [((0,0),[Fw7,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw14,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw21,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw29,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw37,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw42,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw49,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw56,Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b10c0Ok : Fp10b10c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b10c1 : List Entry := [((0,0),[Fw65,Fw98,Fw148,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw159,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw185,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw227,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw268,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw304,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw376,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388,Fw404])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b10c1Ok : Fp10b10c1.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b10c2 : List Entry := [((0,1),[Fw98,Fw101,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b10c2Ok : Fp10b10c2.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b10 : List Entry := Fp10b10c0 ++ Fp10b10c1 ++ Fp10b10c2
def Fp10b12c0 : List Entry := [((0,0),[Fw65,Fw98,Fw139,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b12c0Ok : Fp10b12c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b12 : List Entry := Fp10b12c0
def Fp10b13c0 : List Entry := [((0,0),[Fw65,Fw98,Fw175,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b13c0Ok : Fp10b13c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b13 : List Entry := Fp10b13c0
def Fp10b20c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw358,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b20c0Ok : Fp10b20c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b20 : List Entry := Fp10b20c0
def Fp10b21c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw350,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b21c0Ok : Fp10b21c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b21 : List Entry := Fp10b21c0
def Fp10b22c0 : List Entry := [((0,0),[Fw65,Fw98,Fw193,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw226,Fw239,Fw271,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b22c0Ok : Fp10b22c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b22 : List Entry := Fp10b22c0
def Fp10b24c0 : List Entry := [((0,0),[Fw65,Fw98,Fw142,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b24c0Ok : Fp10b24c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b24 : List Entry := Fp10b24c0
def Fp10b25c0 : List Entry := [((0,0),[Fw65,Fw98,Fw125,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b25c0Ok : Fp10b25c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b25 : List Entry := Fp10b25c0
def Fp10b26c0 : List Entry := [((0,0),[Fw65,Fw98,Fw113,Fw226,Fw239,Fw282,Fw328,Fw388]),
((0,0),[Fw65,Fw98,Fw169,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp10b26c0Ok : Fp10b26c0.all (testRow chart128 configured Ft9 9) = true := by decide +kernel

def Fp10b26 : List Entry := Fp10b26c0
def Fg10 : List (List Entry) := [[], [], Fp10b2, [], Fp10b4, Fp10b5, Fp10b6, Fp10b7, [], [], Fp10b10, [], Fp10b12, Fp10b13, [], [], [], [], [], [], Fp10b20, Fp10b21, Fp10b22, [], Fp10b24, Fp10b25, Fp10b26, [], [], [], [], []]
def Ft10 : Nat → List Entry := bucketOf Fg10
lemma Fv10 : verifiedR configured 11 10 Ft10 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv9
  apply checkBuckets
  simp only [Fg10, Fp10b2, Fp10b4, Fp10b5, Fp10b6, Fp10b7, Fp10b10, Fp10b12, Fp10b13, Fp10b20, Fp10b21, Fp10b22, Fp10b24, Fp10b25, Fp10b26, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, Fp10b2c0Ok, Fp10b4c0Ok, Fp10b5c0Ok, Fp10b6c0Ok, Fp10b7c0Ok, Fp10b10c0Ok, Fp10b10c1Ok, Fp10b10c2Ok, Fp10b12c0Ok, Fp10b13c0Ok, Fp10b20c0Ok, Fp10b21c0Ok, Fp10b22c0Ok, Fp10b24c0Ok, Fp10b25c0Ok, Fp10b26c0Ok]

def Fp11b10c0 : List Entry := [((0,0),[Fw65,Fw98,Fw226,Fw239,Fw282,Fw328,Fw388])]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma Fp11b10c0Ok : Fp11b10c0.all (testRow chart128 configured Ft10 10) = true := by decide +kernel

def Fp11b10 : List Entry := Fp11b10c0
def Fg11 : List (List Entry) := [[], [], [], [], [], [], [], [], [], [], Fp11b10, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def Ft11 : Nat → List Entry := bucketOf Fg11
lemma Fv11 : verifiedR configured 11 11 Ft11 := by
  apply checkedTier chart128 chart128Valid configured (by decide) (by decide) Fv10
  apply checkBuckets
  simp only [Fg11, Fp11b10, List.all_cons, List.all_nil, List.all_append, Bool.true_and, Bool.and_true, Fp11b10c0Ok]

lemma fullChecked {k : Nat} (lim : k ≤ 11) (live : BL k fullRaw.toFinset) : False := by
  have eq := sortFinset fullRaw
  apply Fv11 (0,0) (sortSignals fullRaw) (hit_mem (by decide +kernel)) (by decide +kernel) ?_ k lim
    (eq.symm ▸ live)
  rw [eq]
  intro H u hh q h
  simp [configured, resources] at hh
  rcases hh with h0 | h5
  · rcases h0 with ⟨rfl,rfl⟩
    simpa using M0LB h
  · rcases h5 with ⟨rfl,rfl⟩
    simpa using M5LB h

lemma binary_lower (C : Circuit) (legal : FanInTwo C)
    (spec : ∀x, C.eval (List.ofFn x) = edge x) : 12 ≤ C.gates.countP costly := by
  obtain ⟨k,t,S,cap,run,sub⟩ := tagExtract C.gates raw8 vals legal (output8 legal spec)
  obtain ⟨j,U,le,live,sv⟩ := compress run
  have c : raw8.toFinset.image can ⊆ fullRaw.toFinset := by decide +kernel
  have inc : U ⊆ fullRaw.toFinset := (sv.trans (Finset.image_mono _ sub)).trans c
  obtain ⟨a,l⟩ := live.expand
  have eq := allNeeded l inc FNeed
  by_contra! small
  exact fullChecked (by omega) (eq ▸ live)

def witness : Circuit :=
 ⟨[⟨.or,[0,1]⟩,⟨.and,[0,2]⟩,⟨.or,[8,4]⟩,⟨.or,[1,6]⟩,⟨.or,[7,2]⟩,⟨.or,[7,3]⟩,⟨.or,[3,9]⟩,⟨.and,[12,5]⟩,⟨.or,[9,6]⟩,⟨.and,[11,15]⟩,⟨.or,[14,16]⟩,⟨.and,[13,10]⟩,⟨.or,[17,18]⟩],19⟩
lemma witness_fan : ∀g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma witness_eval (x : Fin 7 → Bool) : witness.eval (List.ofFn x) = edge x := by
  revert x
  decide +kernel

def flatEdges : List ℕ := [0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6]
def tableEdge (x : Fin 7 → Bool) : Bool := decide (∃ i < flatEdges.length / 2,
  (List.ofFn x).getD (flatEdges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (flatEdges.getD (2*i+1) 0) false = true)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma table_match : ∀x, tableEdge x = edge x := by decide +kernel
lemma replacement (gs : List Gate) (o : ℕ)
    (legal : FanInTwo (⟨gs,o⟩ : Circuit))
    (spec : ∀x, (⟨gs,o⟩ : Circuit).eval (List.ofFn x) = tableEdge x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gs.length ∧ ∀ x, (⟨gates',o'⟩ : Circuit).eval (List.ofFn x) = tableEdge x := by
  by_cases n : ∃ g ∈ gs, g.op = .not
  · have lower := binary_lower ⟨gs,o⟩ legal (fun x => (spec x).trans (table_match x))
    change 12 ≤ gs.countP costly at lower
    have strict : gs.countP costly < gs.length := by
      have le := List.countP_le_length (p := costly) (l := gs)
      by_contra! opp
      have all := List.countP_eq_length.mp (Nat.le_antisymm le opp)
      obtain ⟨g,hg,ho⟩ := n
      simpa [costly,ho] using all g hg
    refine ⟨witness.gates,witness.output,witness_fan,?_ ,?_⟩
    · simpa [witness] using (show 13 ≤ gs.length by omega)
    · intro x
      exact (witness_eval x).trans (table_match x).symm
  · refine ⟨gs,o,?_ ,le_rfl,spec⟩
    intro g hg
    have h := legal g hg
    refine ⟨?_ , h.2⟩
    rcases (show g.op = .and ∨ g.op = .or ∨ g.op = .not from h.1) with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (n ⟨g,hg,c⟩).elim

end PEqualNP.Outside.L_meta_10718

theorem PEqualNP.Outside.L_meta_10718 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ spec
  exact PEqualNP.Outside.L_meta_10718.replacement gates o (fun g hg => ⟨show
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)
      from (legal g hg).1, (legal g hg).2⟩) spec
