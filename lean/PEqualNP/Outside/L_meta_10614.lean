import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10614
namespace Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := Nat × Nat
def top : Nat := 0xffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def Valid1 (x : Nat) : Prop := ∀ j, 64 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma top_eq_pow : top = 2 ^ 32 * 2 ^ 32 - 1 := by decide
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 64) := by
  rw [top_eq_pow]; exact pow_add_testBit 32 32 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 64 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 64
  · simp [hj]
  · simp [hj, hx j (by omega)]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 64 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 64 by omega]
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
  have hlt : x < 2 ^ 32 * 2 ^ 32 := by
    have hp : 0 < 2 ^ 32 * 2 ^ 32 := by decide
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
    by_cases hj : j < 64 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 64 <;> simp [hj]
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
def bit (side : Bool) (i : Fin 64) (a : Sig) : Bool :=
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

abbrev I := Fin 64
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
def coord (side : Bool) (i : Nat) := if side then i / 64 * 64 else i % 64
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
def col (x : Nat) := (hop 128 m7 (hop 64 m6 (hop 32 m5 (hop 64 m4 x))))
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
      by_cases hj : j < 64
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
  cases u <;> simp [PEqualNP.Outside.L_meta_10614.Free1868.flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 64 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 64 <;> simp [e]

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
lemma validBound {x} (h : Valid1 x) : x < 2^64 := by
  have eq : x % 2^64 = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < 64
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
abbrev I := Fin 64
def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then PEqualNP.Outside.L_meta_10614.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
open PEqualNP.Outside.L_meta_10614.Board1868 (mult)
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
open PEqualNP.Outside.L_meta_10614.Board1868 (mult)
open PEqualNP.Outside.L_meta_10614.ColorSearch1868 (paint paint_ok)

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
def reindexLoop (f : Fin 64 → Fin 64) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 64 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 64 → Fin 64) (x : Nat) : Nat := reindexLoop f x 64
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindexLoop_testBit (f : Fin 64 → Fin 64) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 64 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 64
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
            have hj414 : j < 64 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 64 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 64
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_testBit (f : Fin 64 → Fin 64) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 64 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 64 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_valid1 (f : Fin 64 → Fin 64) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 64 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_and (f : Fin 64 → Fin 64) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 64 <;> simp [hj, Nat.testBit_and]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_or (f : Fin 64 → Fin 64) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 64 <;> simp [hj, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_bnot (f : Fin 64 → Fin 64) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 64
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_zero (f : Fin 64 → Fin 64) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_top (f : Fin 64 → Fin 64) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 64
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
def pairHom (fp fn : Fin 64 → Fin 64) : SigHom where
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
lemma fixed (p n : Fin 64 → Fin 64) (z : p 0=0) : SignFixed (pairHom p n) := by
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

abbrev I := Fin 64
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
end PEqualNP.Outside.L_meta_10614
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_10614
def edge (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
end PEqualNP.Outside.L_meta_10614
namespace PEqualNP.Outside.L_meta_10614
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
open Projection8403 PEqualNP.Outside.L_meta_10614
namespace Exact8403
def raw8 : List Sig := [(0x21512e25fe338215, 0x8a022808a022808a), (0x4222564ab6de8422, 0x2c10b042c10b042c), (0x84949a937dc58849, 0x3004c013004c0130), (0x828e31c2f6f1082, 0xc027009c027009c0), (0x10cf03e07bf8210c, 0x3800e003800e00), (0x1f0ffe001e4041f0, 0x40010004001000), (0xe00001ffbe407e00, 0x80020008002000)]
def pos8 : Array Nat := #[5, 10, 17, 20, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80, 96, 7, 13, 11, 14, 26, 19, 25, 126, 22, 28, 123, 111, 125, 119, 95, 21, 67, 69, 70, 73, 74, 76, 81, 82, 84, 88, 63, 35, 37, 38, 41, 42, 44, 49, 50, 52, 56]
def neg8 : Array Nat := #[0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 64]
def sample8 (s : Bool) (i : Fin 64) : Fin 7 → Bool :=
  let xs:=if s then pos8 else neg8
  fun j=>(xs.getD (i.val % xs.size) 0).testBit j.val
lemma vals : ∀a∈raw8,Valid a := by
  have h : raw8.all (fun x=>decide (x.1≤top ∧ x.2≤top))=true := by decide +kernel
  intro a ha
  have k:=of_decide_eq_true (List.all_eq_true.mp h a ha)
  exact ⟨valid1_of_le_top k.1,valid1_of_le_top k.2⟩
set_option maxHeartbeats 0 in
lemma good8 : ∀(s : Bool) (i : Fin 64), edge (sample8 s i)=s ∧ List.ofFn (sample8 s i)=raw8.map (bit s i) := by decide +kernel
lemma output8 {C : Circuit} (fan : FanInTwo C) (spec : ∀x, C.eval (List.ofFn x)=edge x) :
    target∈execute C.gates raw8 := by
  let w:=execute C.gates raw8
  have hwv:=execute_valid C.gates raw8 vals
  have hp (s : Bool) (i : Fin 64) : bit s i (w.getD C.output zero)=s := by
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
      by_cases hi : j<64
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)];simp [hi]
    · apply Nat.eq_of_testBit_eq;intro j
      by_cases hi : j<64
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)];exact (Nat.zero_testBit j).symm
  have rep:=get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun h=>h target_proper)
def necessary (v : List Sig) := ∀a∈v,∃p n : Fin 64,∀b∈v,bit true p b≠bit false n b → b=a
lemma allNeeded {k t S} {v : List Sig} (h : Live k t S) (sub : S⊆v.toFinset) (need : necessary v) : S=v.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨p,n,uniq⟩:=need a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩:=PEqualNP.Outside.L_meta_10614.Conflict1868.pair_sep h p n
  exact uniq b (List.mem_toFinset.mp (sub hb)) sep ▸ hb
def necessaryAt (v : List Sig) (pn : List (Nat×Nat)) :=
  (v.zip pn).all fun (a,p,n) => v.all fun b=>bit true (Fin.ofNat 64 p) b == bit false (Fin.ofNat 64 n) b || b==a
lemma needFrom {v : List Sig} {pn : List (Nat×Nat)} (len : v.length≤pn.length) (ok : necessaryAt v pn=true) : necessary v := by
  intro a ha
  obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp ha
  have hp : i<pn.length:=by omega
  have hz : (a,pn[i])∈v.zip pn := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by simp;omega,by simp [eq]⟩
  have h:=List.all_eq_true.mp ok _ hz
  refine ⟨Fin.ofNat 64 pn[i].1,Fin.ofNat 64 pn[i].2,?_⟩
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
def positive (c : Chart) (i : Fin (area c)) : Fin 64 := Fin.ofNat 64 (i.val/c.w)
def negative (c : Chart) (i : Fin (area c)) : Fin 64 := Fin.ofNat 64 (i.val % c.w)
def good (c : Chart) :=
  (∀i : Fin 64, sweep c.spreadP (2^i.val) = if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 64, sweep c.spreadN (2^i.val) = if i.val<c.w then col c i.val else 0) ∧
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
    (hc : f (top ^^^ mask) &&& mask = 0) (bx : PEqualNP.Outside.L_meta_10614.WProof1868.Sub x top)
    (hit : (f x).testBit i=true) : ∃j,x.testBit j=true ∧ mask.testBit j=true := by
  by_contra! hn
  have sub : PEqualNP.Outside.L_meta_10614.WProof1868.Sub x (top ^^^ mask) := by
    intro j hj; simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hh:=PEqualNP.Outside.L_meta_10614.WProof1868.linMono lin sub i hit
  have bad:=congrArg (fun z : Nat=>z.testBit i) hc
  simp [Nat.testBit_and,hh,hm] at bad

theorem pbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadP a).testBit i.val = a.testBit (positive c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10614.WProof1868.validBound va)]
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
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10614.WProof1868.validBound va)]
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
  (∀i : Fin 64,sweep c.spreadP (2^i.val)=if i.val<c.h then row c i.val else 0) ∧
  (∀i : Fin 64,sweep c.spreadN (2^i.val)=if i.val<c.w then col c i.val else 0) ∧
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
open PEqualNP.Outside.L_meta_10614.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_10614.Board1868 (mult)
open PEqualNP.Outside.L_meta_10614.ColorSearch1868 (paint paint_ok)
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
      exact ⟨p,q,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10614.Conflict1868.Unique] using x,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10614.Conflict1868.Unique] using y⟩
end QuickQ
end


open Basis1868 Free1868 FreeSearch1868 Cuts1868 Check2516 Exact8403 Projection8403
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fullRaw : List Sig := raw8.map can
def inp (i : Fin 7) : Sig := fullRaw.getD i.val zero

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma allInp (a : Sig) (ha : a ∈ fullRaw) : ∃ i : Fin 7, a = inp i := by
  obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp ha
  have bound : i < 7 := by simpa [fullRaw, raw8] using hi
  refine ⟨⟨i, bound⟩, ?_⟩
  simpa [inp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using eq.symm
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma inp_mem : ∀ i : Fin 7, inp i ∈ fullRaw := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma inp_eq : ∀ i j : Fin 7, inp i = inp j → i=j := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma init_nonterminal : {can target} ≠ fullRaw.toFinset := by decide +kernel
def pCut (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[22, 1, 18, 3, 23, 19, 24, 5, 6, 7, 8, 10, 11, 12, 13, 14]
  | 1 => #[27, 0, 16, 2, 3, 21, 24, 4, 6, 7, 8, 9, 11, 12, 13, 14]
  | 2 => #[25, 1, 17, 2, 20, 19, 21, 5, 4, 7, 8, 10, 9, 12, 13, 14]
  | 3 => #[28, 0, 15, 2, 3, 20, 23, 4, 6, 5, 8, 9, 11, 10, 13, 14]
  | 4 => #[26, 1, 18, 0, 15, 17, 16, 5, 6, 7, 4, 10, 11, 12, 9, 14]
  | 5 => #[29, 0, 15, 1, 17, 16, 18, 2, 20, 3, 30, 23, 21, 19, 24, 9, 10, 31, 11, 32, 33, 12, 34, 35, 36, 13, 37, 38, 39, 40]
  | _ => #[41, 0, 15, 1, 17, 16, 18, 2, 20, 3, 30, 23, 21, 19, 24, 4, 5, 42, 6, 43, 44, 7, 45, 46, 47, 8, 48, 49, 50, 51]
def nCut (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[0, 2, 4, 5, 6, 8, 9, 10, 11, 12, 13]
  | 1 => #[0, 1, 4, 6, 7, 8, 9, 11, 12, 13]
  | 2 => #[0, 2, 1, 3, 6, 7, 9, 10, 11, 12, 13]
  | 3 => #[0, 1, 4, 2, 3, 5, 9, 10, 12, 13]
  | 4 => #[0, 2, 4, 5, 6, 8, 1, 3, 7, 12, 13]
  | 5 => #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13]
  | _ => #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def minorRaw (i : Fin 7) : List Sig :=
  match i.val with
  | 0 => [(0xf748, 0xffffffffffffff75), (0xeea2, 0xffffffffffffffd3), (0xdd98, 0xfffffffffffffecf), (0xbb86, 0xfffffffffffffe3f), (0x787e, 0xfffffffffffffdff), (0x7fe, 0xfffffffffffffbff)]
  | 1 => [(0xf750, 0xffffffffffffffed), (0xeea8, 0xffffffffffffffdb), (0xdd9a, 0xffffffffffffff47), (0xbb86, 0xffffffffffffff3f), (0x787e, 0xfffffffffffffeff), (0x7fe, 0xfffffffffffffdff)]
  | 2 => [(0xeea2, 0xffffffffffffffd3), (0xf748, 0xffffffffffffff75), (0xdd98, 0xfffffffffffffecf), (0xbb86, 0xfffffffffffffe3f), (0x787e, 0xfffffffffffffdff), (0x7fe, 0xfffffffffffffbff)]
  | 3 => [(0xf750, 0xffffffffffffffed), (0xdd9a, 0xffffffffffffff47), (0xeea8, 0xffffffffffffffdb), (0xbb86, 0xffffffffffffff3f), (0x787e, 0xfffffffffffffeff), (0x7fe, 0xfffffffffffffdff)]
  | 4 => [(0xbb86, 0xfffffffffffffe3f), (0xf748, 0xffffffffffffff75), (0xeea2, 0xffffffffffffffd3), (0xdd98, 0xfffffffffffffecf), (0x787e, 0xfffffffffffffdff), (0x7fe, 0xfffffffffffffbff)]
  | 5 => [(0x3bb56a48, 0xffffffffffffff75), (0x376cd6a2, 0xfffffffffffffbd3), (0x2ee3b198, 0xfffffffffffffecf), (0x1e1f8f86, 0xfffffffffffff63f), (0x1ff807e, 0xfffffffffffff1ff), (0x7ffe, 0xffffffffffffefff)]
  | _ => [(0x3bb56a48, 0xffffffffffffff75), (0x376cd6a2, 0xfffffffffffffbd3), (0x2ee3b198, 0xfffffffffffffecf), (0x1e1f8f86, 0xfffffffffffff63f), (0x1ff807e, 0xfffffffffffff1ff), (0x7ffe, 0xffffffffffffefff)]
def cutPairs (i : Fin 7) : List (Nat × Nat) :=
  match i.val with
  | 0 => [(1, 4), (3, 6), (1, 1), (3, 2), (7, 1), (11, 1)]
  | 1 => [(1, 2), (1, 1), (9, 8), (3, 1), (7, 1), (11, 1)]
  | 2 => [(3, 6), (1, 4), (1, 1), (3, 2), (7, 1), (11, 1)]
  | 3 => [(1, 2), (9, 8), (1, 1), (3, 1), (7, 1), (11, 1)]
  | 4 => [(3, 2), (1, 4), (3, 6), (1, 1), (7, 1), (11, 1)]
  | 5 => [(1, 4), (3, 6), (1, 1), (3, 2), (7, 1), (15, 1)]
  | _ => [(1, 4), (3, 6), (1, 1), (3, 2), (7, 1), (15, 1)]
def pPairs (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[0, 0, 0, 15, 2, 0, 0, 16, 0, 2, 0, 4, 0, 9]
  | 1 => #[1, 17, 0, 0, 1, 18, 5, 1, 1, 19, 1, 5, 1, 10]
  | 2 => #[3, 0, 0, 15, 0, 0, 0, 16, 0, 3, 0, 6, 0, 11]
  | 3 => #[1, 17, 7, 1, 1, 18, 0, 0, 1, 19, 1, 7, 1, 12]
  | 4 => #[3, 2, 2, 20, 2, 3, 2, 21, 0, 0, 2, 8, 2, 13]
  | 5 => #[5, 4, 4, 5, 4, 6, 4, 7, 4, 8, 0, 0, 4, 14]
  | _ => #[10, 9, 9, 10, 9, 11, 9, 12, 9, 13, 9, 14, 0, 0]
def nPairs (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[0, 0, 4, 5, 9, 4, 4, 8, 4, 9, 4, 12, 4, 13]
  | 1 => #[6, 7, 0, 0, 6, 8, 12, 6, 6, 11, 6, 12, 6, 13]
  | 2 => #[9, 1, 1, 3, 0, 0, 1, 7, 1, 9, 1, 12, 1, 13]
  | 3 => #[2, 3, 12, 2, 2, 5, 0, 0, 2, 10, 2, 12, 2, 13]
  | 4 => #[4, 1, 1, 3, 1, 4, 1, 7, 0, 0, 1, 12, 1, 13]
  | 5 => #[2, 1, 1, 2, 1, 4, 1, 6, 1, 9, 0, 0, 1, 13]
  | _ => #[2, 1, 1, 2, 1, 4, 1, 6, 1, 9, 1, 12, 0, 0]

def cut (i : Fin 7) : SigHom :=
  pairHom (fun j => Fin.ofNat 64 ((pCut i).getD j.val ((pCut i).getD 0 0)))
    (fun j => Fin.ofNat 64 ((nCut i).getD (j.val) 0))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma needFull : necessary fullRaw :=
  needFrom (pn := [(0,4), (1,6), (0,1), (1,2), (2,1), (4,1), (9,1)]) (by decide) (by decide +kernel)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma needMinor (i : Fin 7) : necessary (minorRaw i) := by
  apply needFrom (pn := cutPairs i)
  · exact (by decide +kernel : ∀ i, (minorRaw i).length ≤ (cutPairs i).length) i
  · exact (by decide +kernel : ∀ i, necessaryAt (minorRaw i) (cutPairs i) = true) i

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cutImage : ∀ i, (fullRaw.toFinset.image (cut i).fn).image can ⊆
    insert zero (minorRaw i).toFinset := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cutConst : ∀ i : Fin 7, constant ((cut i).fn (inp i)) := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cutBlend : ∀ (i j : Fin 7), i ≠ j → ∀ (d s t : Bool),
    can ((cut i).fn (blend d s t (inp i) (inp j))) ∈
      insert zero (minorRaw i).toFinset := by decide +kernel

def pFor (i j : Fin 7) (d t : Bool) : Fin 64 :=
  Fin.ofNat 64 ((pPairs i).getD (2*j.val + (if (d ^^ t) == sign (raw8.getD j.val zero) then 0 else 1)) 0)
def nFor (i j : Fin 7) (d t : Bool) : Fin 64 :=
  Fin.ofNat 64 ((nPairs i).getD (2*j.val + (if (d ^^ t) == sign (raw8.getD j.val zero) then 0 else 1)) 0)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma otherNoDiff : ∀ (i j : Fin 7) (d t : Bool), i ≠ j → ∀ w : Fin 7,
    w ≠ i → bit true (pFor i j d t) (inp w) = bit false (nFor i j d t) (inp w) := by
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma blendNoDiff : ∀ (i j : Fin 7) (d s t : Bool), i ≠ j →
    bit true (pFor i j d t) (blend d s t (inp i) (inp j)) =
    bit false (nFor i j d t) (blend d s t (inp i) (inp j)) := by
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma retained {k : ℕ} {U : Finset Sig} {i j : Fin 7} {d s t : Bool}
    (ne : i ≠ j) (hU : U ⊆ fullRaw.toFinset)
    (h : BL k (insert (blend d s t (inp i) (inp j)) U)) :
    inp i ∈ U := by
  obtain ⟨q,live⟩ := h.expand
  obtain ⟨w, hw, sep⟩ := Conflict1868.pair_sep live (pFor i j d t) (nFor i j d t)
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact (sep (blendNoDiff i j d s t ne)).elim
  · obtain ⟨m,rfl⟩ := allInp w (List.mem_toFinset.mp (hU hw))
    by_cases hm : m=i
    · simpa [hm] using hw
    · exact (sep (otherNoDiff i j d t ne m hm)).elim

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma first_tail {k : ℕ} {U : Finset Sig} {a b : Sig} {d s t : Bool}
    (he : insert a (insert b U) = fullRaw.toFinset) (ab : a ≠ b)
    (h : BL k (insert (blend d s t a b) U)) :
    ∃ i : Fin 7, ∃ l : ℕ, l + 1 ≤ k ∧ BL l (minorRaw i).toFinset := by
  have ia : a ∈ fullRaw := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self ..)
  have ib : b ∈ fullRaw := List.mem_toFinset.mp
    (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have hU : U ⊆ fullRaw.toFinset := by
    intro x hx
    exact he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  obtain ⟨i,rfl⟩ := allInp _ ia
  obtain ⟨j,rfl⟩ := allInp _ ib
  have ne : i≠j := fun e => ab (congrArg inp e)
  have retain := retained ne hU h
  obtain ⟨l,T,le,hbl,hT⟩ := projectedBL h (cut i)
  have massOne : 1 ≤ mass (cut i) (insert (blend d s t (inp i) (inp j)) U) :=
    Finset.card_pos.mpr ⟨inp i, Finset.mem_filter.mpr
      ⟨Finset.mem_insert_of_mem retain, cutConst i⟩⟩
  have sub : T ⊆ insert zero (minorRaw i).toFinset := by
    apply hT.trans
    simp only [Finset.image_insert, Finset.insert_subset_iff]
    exact ⟨cutBlend i j ne d s t, (Finset.image_mono _ (Finset.image_mono _ hU)).trans (cutImage i)⟩
  have incl : T ⊆ (minorRaw i).toFinset := by
    intro x hx
    exact (Finset.mem_insert.mp (sub hx)).resolve_left (hbl.forms x hx).1.2.1
  obtain ⟨q,live⟩ := hbl.expand
  have hEq := allNeeded live incl (needMinor i)
  exact ⟨i,l,by omega,hEq ▸ hbl⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma first_drop {k : ℕ} (h : BL k fullRaw.toFinset) :
    ∃ i : Fin 7, ∃ l : ℕ, l + 2 ≤ k ∧ BL l (minorRaw i).toFinset := by
  generalize he : fullRaw.toFinset = S at h
  cases h with
  | stop => exact (init_nonterminal he.symm).elim
  | step _ _ _ _ ab _ tail =>
    obtain ⟨i,l,le,h⟩ := first_tail he.symm ab tail
    exact ⟨i,l,by omega,h⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma conditional_binary_lower
    (excluded : ∀ (i : Fin 7) (l : ℕ), l ≤ 10 → ¬ BL l (minorRaw i).toFinset)
    (C : Circuit) (legal : FanInTwo C)
    (spec : ∀ x, C.eval (List.ofFn x) = edge x) : 13 ≤ C.gates.countP costly := by
  obtain ⟨k,t,S,cap,run,sub⟩ := tagExtract C.gates raw8 vals legal (output8 legal spec)
  obtain ⟨j,T,le,hbl,incl⟩ := compress run
  have allSub : T ⊆ fullRaw.toFinset := by
    apply incl.trans
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,sub _ ha,rfl⟩)
  obtain ⟨q,h⟩ := hbl.expand
  have hEq := allNeeded h allSub needFull
  obtain ⟨i,l,ml,mlive⟩ := first_drop (hEq ▸ hbl)
  by_contra! small
  exact excluded i l (by omega) mlive

def representative (i : Fin 7) : Fin 7 :=
  if i=1 ∨ i=3 then 1 else if i=5 ∨ i=6 then 5 else 0

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma representative_eq : ∀ i, (minorRaw i).toFinset =
    (minorRaw (representative i)).toFinset := by decide +kernel

end PEqualNP.Outside.L_meta_10614

namespace PEqualNP.Outside.L_meta_10614

open Basis1868 Free1868 FreeSearch1868

def oriented (u : Bool) (a : Sig) (p n : Fin 64) :=
  (bit true p a ^^ u) && !(bit false n a ^^ u)

def unate (S : Finset Sig) := ∃ pol : Sig → Bool, ∀ p n : Fin 64,
  ∃ a ∈ S, oriented (pol a) a p n = true

lemma oriented_step : ∀ (o l r d ap an bp bn : Bool),
    (((if d then (ap ^^ l) || (bp ^^ r) else (ap ^^ l) && (bp ^^ r)) ^^ o) &&
      !((if d then (an ^^ l) || (bn ^^ r) else (an ^^ l) && (bn ^^ r)) ^^ o)) = true →
    ((ap ^^ (l ^^ o)) && !(an ^^ (l ^^ o))) = true ∨
    ((bp ^^ (r ^^ o)) && !(bn ^^ (r ^^ o))) = true := by decide +kernel

lemma bit_flip (s q : Bool) (i : Fin 64) {a : Sig} (va : Valid a) :
    bit q i (flip s a) = (bit q i a ^^ s) := by
  cases s
  · simp [Free1868.flip]
  · rw [show Free1868.flip true a = neg a from rfl, bit_neg q i va]
    cases bit q i a <;> rfl

lemma liveCardLocal {n : ℕ} {S : Finset Sig} (live : BL n S) : S.card ≤ n + 1 := by
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

lemma unate_of_full {k : ℕ} {S : Finset Sig} (h : BL k S) (tight : S.card = k+1) :
    unate S := by
  induction h with
  | stop =>
    refine ⟨fun _ => true, fun p n => ⟨can target, by simp, ?_⟩⟩
    exact (by decide +kernel : ∀ p n : Fin 64, oriented true (can target) p n = true) p n
  | @step k U a b d s t ha hb ca cb hab fresh tail ih =>
    let g := bin d (flip s a) (flip t b)
    let z := can g
    have vg : Valid g := valid_bin (vf s ha.1) (vf t hb.1)
    have nz : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have tailBound := liveCardLocal tail
    change (insert z U).card ≤ k + 1 at tailBound
    rw [Finset.card_insert_of_notMem nz] at tailBound
    have nu : U.card ≤ k := by omega
    have aa : a ∉ U := by
      intro h
      have h1 : a ∈ insert b U := Finset.mem_insert_of_mem h
      have h2 := Finset.card_insert_le (s := U) (a := b)
      rw [Finset.insert_eq_of_mem h1] at tight
      omega
    have bb : b ∉ U := by
      intro h
      have h1 := Finset.card_insert_le (s := U) (a := a)
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    have ab : a ∉ insert b U := by simp [hab, aa]
    rw [Finset.card_insert_of_notMem ab, Finset.card_insert_of_notMem bb] at tight
    have tailTight : (insert z U).card = k+1 := by
      rw [Finset.card_insert_of_notMem nz]
      omega
    obtain ⟨pol, cover⟩ := ih tailTight
    let o := sign g ^^ pol z
    let qpol := fun x => if x = a then s ^^ o else if x = b then t ^^ o else pol x
    refine ⟨qpol, fun p n => ?_⟩
    obtain ⟨w, wm, sep⟩ := cover p n
    rcases Finset.mem_insert.mp wm with rfl | wu
    · have sz (q : Bool) (i : Fin 64) : bit q i z = (bit q i g ^^ sign g) :=
        bit_flip (sign g) q i vg
      change oriented (pol z) z p n = true at sep
      simp only [oriented, sz, g, bit_bin, bit_flip _ _ _ ha.1, bit_flip _ _ _ hb.1] at sep
      simp only [Bool.xor_assoc] at sep
      rcases oriented_step o s t d _ _ _ _ sep with ax | bx
      · exact ⟨a, Finset.mem_insert_self .., by simpa [qpol, oriented] using ax⟩
      · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), by
          simpa [qpol, oriented, hab.symm] using bx⟩
    · have xa : w ≠ a := fun e => aa (e ▸ wu)
      have xb : w ≠ b := fun e => bb (e ▸ wu)
      exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem wu), by
        simpa [qpol, xa, xb] using sep⟩

end PEqualNP.Outside.L_meta_10614

namespace PEqualNP.Outside.L_meta_10614

open Basis1868 Free1868

def polarBoard (c : QuickQ.Chart) (a : Sig) (u : Bool) : Nat :=
  (QuickQ.diff c false (Free1868.flip u a)).2

def polarChoices (c : QuickQ.Chart) (a : Sig) : Nat × Nat :=
  (polarBoard c a false, polarBoard c a true)

def coverSearch (r prior : Nat) : List (Nat × Nat) → Bool
  | [] => prior &&& r == r
  | (a,b) :: rest => (prior &&& r == r) ||
      coverSearch r (prior ||| a) rest || coverSearch r (prior ||| b) rest

def coverBits (c : QuickQ.Chart) (pol : Sig → Bool) : List Sig → Nat
  | [] => 0
  | a :: v => polarBoard c a (pol a) ||| coverBits c pol v

lemma coverRun (c : QuickQ.Chart) (pol : Sig → Bool) (r prior : Nat) (v : List Sig)
    (hw : ((prior ||| coverBits c pol v) &&& r) = r) :
    coverSearch r prior (v.map (polarChoices c)) = true := by
  induction v generalizing prior with
  | nil => simpa [coverSearch, coverBits] using hw
  | cons a v ih =>
    by_cases ha : pol a
    · simp only [coverBits, ha, ← Nat.or_assoc] at hw
      have yes := ih _ hw
      simp [coverSearch, polarChoices, yes]
    · simp only [Bool.eq_false_iff.mpr ha, coverBits, ← Nat.or_assoc] at hw
      have yes := ih _ hw
      simp [coverSearch, polarChoices, yes]

lemma orientBoard {c : QuickQ.Chart} (hg : QuickQ.good c) {a : Sig} (va : Valid a)
    (u : Bool) (i : Fin (QuickQ.area c)) :
    (polarBoard c a u).testBit i.val = true ↔
      oriented u a (QuickQ.positive c i) (QuickQ.negative c i) = true := by
  have eq := QuickQ.diffBit hg false (vf u va) i
  rw [polarBoard, eq]
  change (Free1868.flip u a).1.testBit (QuickQ.positive c i).val = true ∧
      (Free1868.flip u a).2.testBit (QuickQ.negative c i).val = false ↔
        oriented u a _ _ = true
  unfold oriented
  rw [← bit_flip u true _ va, ← bit_flip u false _ va]
  simp [bit]

lemma coverHit {c : QuickQ.Chart} {pol : Sig → Bool} {v : List Sig} {a : Sig}
    (ha : a ∈ v) (i : Nat) (hit : (polarBoard c a (pol a)).testBit i = true) :
    (coverBits c pol v).testBit i = true := by
  induction v with
  | nil => simp at ha
  | cons b v ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [coverBits, Nat.testBit_or, hit]
    · simp [coverBits, Nat.testBit_or, ih ha]

def unateTest (c : QuickQ.Chart) (v : List Sig) : Bool :=
  coverSearch (QuickQ.roof c) 0 (v.map (polarChoices c))

lemma unateTest_complete {c : QuickQ.Chart} (hg : QuickQ.good c) {v : List Sig}
    (va : ∀ a ∈ v, Valid a) (h : unate v.toFinset) :
    unateTest c v = true := by
  obtain ⟨pol, ht⟩ := h
  apply coverRun c pol
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.zero_or, Nat.testBit_and, QuickQ.roofBit]
  by_cases hj : j < QuickQ.area c
  · let i : Fin (QuickQ.area c) := ⟨j,hj⟩
    obtain ⟨a,ha,sep⟩ := ht (QuickQ.positive c i) (QuickQ.negative c i)
    have m := List.mem_toFinset.mp ha
    have bit := (orientBoard hg (va a m) (pol a) i).mpr sep
    simp only [show decide (j < QuickQ.area c) = true from decide_eq_true hj, Bool.and_true]
    exact coverHit m _ bit
  · simp [hj]

end PEqualNP.Outside.L_meta_10614
namespace PEqualNP.Outside.L_meta_10614
namespace Orbit10614
open Basis1868 Free1868 FreeSearch1868 Cuts1868 Sym1868

abbrev PermRows := Array Nat × Array Nat

def position (a : Array Nat) (i : Fin 64) : Fin 64 := Fin.ofNat 64 (a.getD i.val i.val)

def orbitHom (g : PermRows) : SigHom := pairHom (position g.1) (position g.2)

def orbitMap (g : PermRows) (a : Sig) : Sig := (orbitHom g).fn a

def orbitWord (a : Array Nat) (x : Nat) : Nat :=
  let m := min a.size 64
  reindexLoop (position a) x m ||| (x &&& ((2^64-1) ^^^ (2^m-1)))

lemma orbitWord_eq (a : Array Nat) (x : Nat) : orbitWord a x = reindex (position a) x := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [orbitWord,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one,reindexLoop_testBit,reindex_testBit]
  by_cases bounded : j < 64
  · by_cases stored : j < a.size
    · have within : j < min a.size 64 := by omega
      simp [within,bounded]
    · have beyond : ¬j < min a.size 64 := by omega
      have eq : position a ⟨j,bounded⟩ = ⟨j,bounded⟩ := by
        apply Fin.ext
        simp [position,Array.getD,Nat.mod_eq_of_lt bounded,stored]
      simp [beyond,bounded,eq]
  · have beyond : ¬j < min a.size 64 := by omega
    simp [beyond,bounded]

def fastOrbitMap (g : PermRows) (a : Sig) : Sig :=
  (orbitWord g.1 a.1,orbitWord g.2 a.2)

lemma fastOrbitMap_eq (g : PermRows) (a : Sig) : fastOrbitMap g a = orbitMap g a :=
  Prod.ext (orbitWord_eq _ _) (orbitWord_eq _ _)

def rowsInverse (g inv : PermRows) : Bool :=
  (List.finRange 64).all fun i =>
    position g.1 (position inv.1 i) == i && position g.2 (position inv.2 i) == i

def checkGroup (group : List PermRows) : Bool := group.all fun g =>
  position g.1 0 == 0 && group.any fun inv => rowsInverse g inv

def GroupGood (group : List PermRows) : Prop := ∀ g ∈ group, ∃ inv : PermRows,
  position g.1 0 = 0 ∧ rowsInverse g inv = true

lemma group_checked {group : List PermRows} (h : checkGroup group = true) : GroupGood group := by
  intro g hg
  have q := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true,beq_iff_eq] at q
  obtain ⟨inv,_,hi⟩ := List.any_eq_true.mp q.2
  exact ⟨inv,q.1,hi⟩

private lemma row_inverse {g inv : Array Nat} (h : ∀ i : Fin 64, position g (position inv i) = i)
    {x : Nat} (valid : Valid1 x) : reindex (position inv) (reindex (position g) x) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [reindex_testBit]
  split
  next hj =>
    rw [reindex_testBit, dite_eq_left (position inv ⟨j,hj⟩).isLt, h]
  next hj =>
    exact (valid j (Nat.le_of_not_gt hj)).symm

lemma orbit_inverse {g inv : PermRows} (h : rowsInverse g inv = true) {a : Sig} (va : Valid a) :
    orbitMap inv (orbitMap g a) = a := by
  have c (i : Fin 64) :
      position g.1 (position inv.1 i) = i ∧ position g.2 (position inv.2 i) = i := by
    have p := List.all_eq_true.mp h i (by simp)
    simpa only [Bool.and_eq_true,beq_iff_eq] using p
  exact Prod.ext (row_inverse (fun i => (c i).1) va.1)
    (row_inverse (fun i => (c i).2) va.2)

def signalKey (s : Sig) : Nat := s.1 * 2^64 + s.2

def insertSignal (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b::bs => if signalKey a ≤ signalKey b then a::b::bs else b::insertSignal a bs

def sortSignals : List Sig → List Sig
  | [] => []
  | a::as => insertSignal a (sortSignals as)

private lemma insertSignal_perm (a : Sig) (w : List Sig) : (insertSignal a w).Perm (a::w) := by
  induction w with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : signalKey a ≤ signalKey b
    · simp [insertSignal,h]
    · simpa [insertSignal,h] using (List.Perm.cons b ih).trans (.swap a b bs)

lemma sort_perm (v : List Sig) : (sortSignals v).Perm v := by
  induction v with
  | nil => exact .refl _
  | cons a bs ih => exact (insertSignal_perm a (sortSignals bs)).trans (.cons a ih)

lemma sort_set (v : List Sig) : (sortSignals v).toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (sort_perm v).mem_iff (a:=a)

def orbitHit (group : List PermRows) (lookup : List Sig → Bool) (v : List Sig) : Bool :=
  lookup (sortSignals v) || group.any (fun g => lookup (sortSignals (v.map (fastOrbitMap g))))

def ordinaryPass (c : QuickQ.Chart) (n : ℕ) (v : List Sig) : Bool :=
  (v.length ≤ n+1) && QuickQ.test c true (n+2-v.length) v &&
  (v.length != n+1 || unateTest c v)

def absentOrbit (c : QuickQ.Chart) (group : List PermRows) (n : ℕ)
    (lookup : List Sig → Bool) (v : List Sig) : Bool :=
  ordinaryPass c n v && !orbitHit group lookup v

def rowCheck (c : QuickQ.Chart) (group : List PermRows) (n : ℕ)
    (lookup : List Sig → Bool) (v : List Sig) : Bool :=
  !(baseTest v || scanPairs (pairB v (absentOrbit c group n lookup)) v)

section
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
  let g:=PEqualNP.Outside.L_meta_10614.Board1868.mult s
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
open Board1868 (mult)
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
    m≤k+1 && zs.any (passes c lookup (k+2-m) m rest (mult rest))
lemma swapOrder {α β : Type} (xs : List α) (ys : List β) (p : α→β→Bool) :
    (xs.any fun x=>ys.any (p x))=(ys.any fun y=>xs.any (fun x=>p x y)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨x,hx,y,hy,h⟩ <;> exact ⟨y,hy,x,hx,h⟩
lemma passHead (c k lookup rest a) : pass c k lookup (a::rest)=
    (rest.length+1≤k+1 && passes c lookup (k+2-(rest.length+1)) (rest.length+1) rest (mult rest) a) := by
  simp only [pass,testRows,passes,List.length_cons,List.map_cons,mult,Bool.and_assoc]
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

end

def branchHit (c : QuickQ.Chart) (group : List PermRows) (n : Nat)
    (lookup : List Sig → Bool) (w : List Sig) : Bool :=
  !(w.length != n+1 || unateTest c w) || orbitHit group lookup w

lemma plainBranch (c : QuickQ.Chart) (group : List PermRows) (n : Nat)
    (lookup : List Sig → Bool) (w : List Sig) :
    PackQ.plain c true n (branchHit c group n lookup) w =
      absentOrbit c group n lookup w := by
  unfold PackQ.plain branchHit absentOrbit ordinaryPass
  cases hu : (w.length != n+1 || unateTest c w) <;>
    cases ho : orbitHit group lookup w <;> simp [hu,ho,Bool.and_assoc]

def rowCheckFast (c : QuickQ.Chart) (group : List PermRows) (n : Nat)
    (lookup : List Sig → Bool) (v : List Sig) : Bool :=
  let ws := v.map (QuickQ.diff c true)
  !(baseTest v || scanPairs (GroupQ.fork c true n (branchHit c group n lookup) v ws) ws)

lemma rowCheckFast_eq (c : QuickQ.Chart) (group : List PermRows) (n : Nat)
    (lookup : List Sig → Bool) (v : List Sig) :
    rowCheckFast c group n lookup v = rowCheck c group n lookup v := by
  let ws := v.map (QuickQ.diff c true)
  let code := branchHit c group n lookup
  have e : GroupQ.fork c true n code v ws = PackQ.forkS c n code ws v := by
    funext a b
    exact GroupQ.forkSEQ c n code v ws a b
  unfold rowCheckFast rowCheck
  change (!(baseTest v || scanPairs (GroupQ.fork c true n code v ws) ws)) = _
  rw [e, show ws = v.map (QuickQ.diff c true) from rfl]
  rw [PackQ.scanMap _ _ _ (PackQ.forkSMap _ _ _ _)]
  rw [show PackQ.plain c true n code = absentOrbit c group n lookup from
    funext (plainBranch c group n lookup)]

def checkRows (c : QuickQ.Chart) (group : List PermRows) (n : ℕ)
    (lookup : List Sig → Bool) (rows : List (List Sig)) : Bool :=
  rows.all (rowCheckFast c group n lookup)

def verified (tiers : Nat → List (List Sig)) (n : Nat) : Prop :=
  ∀ v ∈ tiers n, v.Nodup → ∀ k ≤ n, ¬ BL k v.toFinset

lemma verificationStart {tiers : Nat → List (List Sig)} (empty : tiers 0 = []) : verified tiers 0 := by
  simp [verified,empty]

private lemma orbit_no_hit {group tiers n lookup w m} (good : GroupGood group)
    (sound : ∀ v, lookup v = true → v ∈ tiers n) (previous : verified tiers n)
    (nd : w.Nodup) (cap : m ≤ n) (live : BL m w.toFinset) :
    orbitHit group lookup w = false := by
  cases ht : orbitHit group lookup w
  · rfl
  · exfalso
    have map_eq (g : PermRows) : fastOrbitMap g = orbitMap g := funext (fastOrbitMap_eq g)
    have positive : lookup (sortSignals w) = true ∨
        (group.any fun g => lookup (sortSignals (w.map (orbitMap g)))) = true :=
      Bool.or_eq_true_iff.mp (by simpa only [orbitHit,map_eq] using ht)
    rcases positive with old | shifted
    · exact previous _ (sound _ old) ((sort_perm w).nodup_iff.mpr nd) m cap
        ((sort_set w).symm ▸ live)
    · obtain ⟨g,hg,hit⟩ := List.any_eq_true.mp shifted
      obtain ⟨inv,zeroFixed,invGood⟩ := good g hg
      have goodW (a : Sig) (ha : a ∈ w) : Good (orbitHom g) (orbitHom inv) a :=
        let va := (live.forms a (List.mem_toFinset.mpr ha)).1.1
        ⟨va,orbit_inverse invGood va⟩
      have rotated := Moves3400.mapBL (J:=orbitHom inv) (Moves3400.fixed _ _ zeroFixed)
        live (fun a ha => goodW a (List.mem_toFinset.mp ha))
      have same : (sortSignals (w.map (orbitMap g))).toFinset =
          w.toFinset.image (orbitHom g).fn := by
        rw [sort_set]
        ext a
        simp [orbitMap]
      have nodupMap : (w.map (orbitMap g)).Nodup :=
        List.Nodup.map_on (fun a ha b hb eq => Sym1868.inj (goodW a ha) (goodW b hb) eq) nd
      exact previous _ (sound _ hit) ((sort_perm _).nodup_iff.mpr nodupMap) m cap (same.symm ▸ rotated)

lemma ordinaryPass_complete {c : QuickQ.Chart} {n m : ℕ} {w : List Sig} (chart : QuickQ.good c)
    (nd : w.Nodup) (cap : m ≤ n) (live : BL m w.toFinset) :
    ordinaryPass c n w = true := by
  have sz := liveCardLocal live
  rw [List.toFinset_card_of_nodup nd] at sz
  have le : w.length ≤ n+1 := by omega
  have color := QuickQ.testSigned chart cap nd live
  have value := fun a (ha : a ∈ w) => (live.forms a (List.mem_toFinset.mpr ha)).1.1
  by_cases edge : w.length = n+1
  · have tight : w.toFinset.card = m+1 := by rw [List.toFinset_card_of_nodup nd]; omega
    have polar := unateTest_complete chart value (unate_of_full live tight)
    have colorT : QuickQ.test c true 1 w = true := by simpa [edge] using color
    simp [ordinaryPass,edge,colorT,polar]
  · simp [ordinaryPass,le,color,edge]

lemma verificationStep {c : QuickQ.Chart} {group tiers n lookup}
    (chart : QuickQ.good c) (good : GroupGood group)
    (lookupSound : ∀ v, lookup v = true → v ∈ tiers n)
    (previous : verified tiers n)
    (checked : checkRows c group n lookup (tiers (n+1)) = true) : verified tiers (n+1) := by
  intro v hv nd k cap live
  have stay : ∀ w : List Sig, w.Nodup → ∀ m ≤ n,
      BL m w.toFinset → absentOrbit c group n lookup w = true := by
    intro w wn m lm hw
    simp [absentOrbit, ordinaryPass_complete chart wn lm hw,
      orbit_no_hit good lookupSound previous wn lm hw]
  have reach := oneStep live n cap v nd rfl (absentOrbit c group n lookup) stay
  have bad := List.all_eq_true.mp checked v hv
  rw [rowCheckFast_eq] at bad
  change (!(baseTest v || scanPairs (pairB v (absentOrbit c group n lookup)) v)) = true at bad
  simp [reach] at bad

end Orbit10614
end PEqualNP.Outside.L_meta_10614
namespace PEqualNP.Outside.L_meta_10614
open Basis1868 Free1868 FreeSearch1868 Cuts1868
namespace Cert10614
open Orbit10614
def chart16 : QuickQ.Chart := ⟨16,16,[(false, 0, 0xffff), (true, 120, 0xff000000000000000000000000000000ff), (true, 60, 0xf000000000000000f000000000000000f000000000000000f), (true, 30, 0x300000003000000030000000300000003000000030000000300000003), (true, 15, 0x1000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0x1000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma chart_valid16 : QuickQ.good chart16 := by
  apply QuickQ.goodOfCompact
  unfold QuickQ.compactGood
  decide +kernel
def chart32 : QuickQ.Chart := ⟨32,16,[(false, 0, 0xffffffff), (true, 240, 0xffff000000000000000000000000000000000000000000000000000000000000ffff), (true, 120, 0xff000000000000000000000000000000ff000000000000000000000000000000ff000000000000000000000000000000ff), (true, 60, 0xf000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f), (true, 30, 0x3000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003), (true, 15, 0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 512, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 512, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 256, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 512, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma chart_valid32 : QuickQ.good chart32 := by
  apply QuickQ.goodOfCompact
  unfold QuickQ.compactGood
  decide +kernel
def hashBucket (w : List Sig) : Nat :=
  (w.foldl (fun s a => s + a.1 * 31 + a.2 * 11) 0) % 31

def bucketHas (w : List Sig) : List (List (List Sig)) → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b.contains w
  | _ :: bs, i + 1 => bucketHas w bs i

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma bucketHas_sound (w : List Sig) (v : List (List (List Sig))) (i : Nat)
    (h : bucketHas w v i = true) : w ∈ v.flatten := by
  induction v generalizing i with
  | nil => simp [bucketHas] at h
  | cons b v ih =>
    cases i with
    | zero =>
      have mem : w ∈ b := List.contains_iff_mem.mp (by simpa [bucketHas] using h)
      exact List.mem_flatten.mpr ⟨b, by simp, mem⟩
    | succ i =>
      have mem : w ∈ v.flatten := ih i (by simpa [bucketHas] using h)
      obtain ⟨bs, hs, hw⟩ := List.mem_flatten.mp mem
      exact List.mem_flatten.mpr ⟨bs, by simp [hs], hw⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma checkFlatten (c : QuickQ.Chart) (group : List PermRows) (n : Nat)
    (lookup : List Sig → Bool) (rows : List (List (List Sig))) :
    checkRows c group n lookup rows.flatten = rows.all (checkRows c group n lookup) := by
  simp only [checkRows, List.all_flatten] <;> rfl

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma checkEmpty (c : QuickQ.Chart) (group : List PermRows) (n : Nat)
    (lookup : List Sig → Bool) : checkRows c group n lookup [] = true := rfl


namespace Minor0
def group : List PermRows := [
  (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
  (#[0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 7, 8, 9, 10, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 9]),
  (#[0, 1, 5, 3, 4, 2, 6, 7, 10, 9, 8, 11, 14, 13, 12, 15], #[0, 1, 6, 7, 4, 8, 2, 3, 5, 9, 10]),
  (#[0, 1, 5, 3, 4, 2, 6, 11, 14, 13, 12, 7, 10, 9, 8, 15], #[0, 1, 6, 7, 4, 8, 2, 3, 5, 10, 9]),
  (#[0, 3, 4, 1, 2, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 15], #[0, 2, 1, 3, 6, 7, 4, 5, 8, 9, 10]),
  (#[0, 3, 4, 1, 2, 6, 5, 12, 11, 14, 13, 8, 7, 10, 9, 15], #[0, 2, 1, 3, 6, 7, 4, 5, 8, 10, 9]),
  (#[0, 3, 6, 1, 2, 4, 5, 8, 9, 10, 7, 12, 13, 14, 11, 15], #[0, 2, 4, 5, 6, 8, 1, 3, 7, 9, 10]),
  (#[0, 3, 6, 1, 2, 4, 5, 12, 13, 14, 11, 8, 9, 10, 7, 15], #[0, 2, 4, 5, 6, 8, 1, 3, 7, 10, 9]),
  (#[0, 1, 2, 3, 6, 5, 4, 9, 8, 7, 10, 13, 12, 11, 14, 15], #[0, 4, 2, 5, 1, 3, 6, 8, 7, 9, 10]),
  (#[0, 1, 2, 3, 6, 5, 4, 13, 12, 11, 14, 9, 8, 7, 10, 15], #[0, 4, 2, 5, 1, 3, 6, 8, 7, 10, 9]),
  (#[0, 1, 5, 3, 6, 2, 4, 9, 10, 7, 8, 13, 14, 11, 12, 15], #[0, 4, 6, 8, 1, 7, 2, 5, 3, 9, 10]),
  (#[0, 1, 5, 3, 6, 2, 4, 13, 14, 11, 12, 9, 10, 7, 8, 15], #[0, 4, 6, 8, 1, 7, 2, 5, 3, 10, 9]),
  (#[0, 3, 4, 1, 5, 6, 2, 10, 7, 8, 9, 14, 11, 12, 13, 15], #[0, 6, 1, 7, 2, 3, 4, 8, 5, 9, 10]),
  (#[0, 3, 4, 1, 5, 6, 2, 14, 11, 12, 13, 10, 7, 8, 9, 15], #[0, 6, 1, 7, 2, 3, 4, 8, 5, 10, 9]),
  (#[0, 3, 6, 1, 5, 4, 2, 10, 9, 8, 7, 14, 13, 12, 11, 15], #[0, 6, 4, 8, 2, 5, 1, 7, 3, 9, 10]),
  (#[0, 3, 6, 1, 5, 4, 2, 14, 13, 12, 11, 10, 9, 8, 7, 15], #[0, 6, 4, 8, 2, 5, 1, 7, 3, 10, 9])]
def s0 : Sig := (0x6, 0xfffffffffffff83f)
def s1 : Sig := (0x18, 0xfffffffffffff8cf)
def s2 : Sig := (0x1e, 0xfffffffffffff8ff)
def s3 : Sig := (0x26, 0xfffffffffffff9ff)
def s4 : Sig := (0x36, 0x8a)
def s5 : Sig := (0x7e, 0xfffffffffffff9ff)
def s6 : Sig := (0x86, 0xa)
def s7 : Sig := (0xb6, 0x8a)
def s8 : Sig := (0xfe, 0xfffffffffffff9ff)
def s9 : Sig := (0x180, 0xfffffffffffffa0f)
def s10 : Sig := (0x184, 0xfffffffffffffa2f)
def s11 : Sig := (0x186, 0xfffffffffffffa0f)
def s12 : Sig := (0x186, 0xfffffffffffffa3f)
def s13 : Sig := (0x1b6, 0xfffffffffffffa8f)
def s14 : Sig := (0x1fe, 0xae)
def s15 : Sig := (0x1fe, 0xfffffffffffff9ff)
def s16 : Sig := (0x1fe, 0xfffffffffffffbff)
def s17 : Sig := (0x282, 0xfffffffffffffa13)
def s18 : Sig := (0x2fe, 0xfffffffffffff9ff)
def s19 : Sig := (0x380, 0x200)
def s20 : Sig := (0x380, 0xfffffffffffffa0f)
def s21 : Sig := (0x380, 0xfffffffffffffa3f)
def s22 : Sig := (0x386, 0xfffffffffffffa3f)
def s23 : Sig := (0x3b6, 0xfffffffffffffabf)
def s24 : Sig := (0x3de, 0xfffffffffffffa3f)
def s25 : Sig := (0x3fe, 0xfffffffffffffbff)
def s26 : Sig := (0x580, 0xfffffffffffffacf)
def s27 : Sig := (0x598, 0xfffffffffffffacf)
def s28 : Sig := (0x5be, 0xfffffffffffffacf)
def s29 : Sig := (0x5dc, 0xfffffffffffffaef)
def s30 : Sig := (0x5f8, 0xfffffffffffffbcf)
def s31 : Sig := (0x5fe, 0xfffffffffffffbff)
def s32 : Sig := (0x6a2, 0xfffffffffffffbd3)
def s33 : Sig := (0x748, 0xfffffffffffffb75)
def s34 : Sig := (0x780, 0x200)
def s35 : Sig := (0x780, 0xfffffffffffffa0f)
def s36 : Sig := (0x786, 0xfffffffffffffa3f)
def s37 : Sig := (0x798, 0xfffffffffffffacf)
def s38 : Sig := (0x79e, 0xfffffffffffffaff)
def s39 : Sig := (0x7a6, 0xfffffffffffffbff)
def s40 : Sig := (0x7b6, 0x28a)
def s41 : Sig := (0x7d8, 0xfffffffffffffbff)
def s42 : Sig := (0x7fe, 0x2ae)
def s43 : Sig := (0x7fe, 0xfffffffffffffbff)
def s44 : Sig := (0x87e, 0xfffffffffffff9ff)
def s45 : Sig := (0x886, 0xa)
def s46 : Sig := (0x886, 0xfffffffffffff83f)
def s47 : Sig := (0x890, 0x8a)
def s48 : Sig := (0x8a2, 0x82)
def s49 : Sig := (0x8a6, 0x8a)
def s50 : Sig := (0x8b6, 0x8a)
def s51 : Sig := (0x8fe, 0xfffffffffffff9ff)
def s52 : Sig := (0x980, 0xfffffffffffffa0f)
def s53 : Sig := (0x986, 0xfffffffffffffa0f)
def s54 : Sig := (0x990, 0xfffffffffffffa8f)
def s55 : Sig := (0xb86, 0xfffffffffffffa3f)
def s56 : Sig := (0xd98, 0xfffffffffffffacf)
def s57 : Sig := (0xffe, 0xfffffffffffffbff)
def s58 : Sig := (0x1598, 0xfffffffffffffacf)
def s59 : Sig := (0x1800, 0xfffffffffffffc0f)
def s60 : Sig := (0x1804, 0xfffffffffffffc2f)
def s61 : Sig := (0x1806, 0xfffffffffffffc3f)
def s62 : Sig := (0x1980, 0x600)
def s63 : Sig := (0x1980, 0xfffffffffffffe0f)
def s64 : Sig := (0x1986, 0x2e)
def s65 : Sig := (0x19fe, 0xffffffffffffffff)
def s66 : Sig := (0x1b86, 0xfffffffffffffe3f)
def s67 : Sig := (0x2222, 0x110)
def s68 : Sig := (0x2240, 0x130)
def s69 : Sig := (0x2386, 0xfffffffffffffa3f)
def s70 : Sig := (0x2b86, 0xfffffffffffffe3f)
def s71 : Sig := (0x3000, 0xfffffffffffffc35)
def s72 : Sig := (0x3806, 0xfffffffffffffc3f)
def s73 : Sig := (0x3836, 0xfffffffffffffcbf)
def s74 : Sig := (0x385e, 0xfffffffffffffc3f)
def s75 : Sig := (0x387e, 0xfffffffffffffdff)
def s76 : Sig := (0x3886, 0xfffffffffffffc3f)
def s77 : Sig := (0x3906, 0xfffffffffffffc3f)
def s78 : Sig := (0x3a06, 0xfffffffffffffc3f)
def s79 : Sig := (0x3b80, 0x600)
def s80 : Sig := (0x3b86, 0xfffffffffffffe3f)
def s81 : Sig := (0x3bb6, 0x68a)
def s82 : Sig := (0x3f80, 0x600)
def s83 : Sig := (0x3ffe, 0xffffffffffffffff)
def s84 : Sig := (0x4418, 0xc0)
def s85 : Sig := (0x4420, 0x1c0)
def s86 : Sig := (0x4c98, 0xca)
def s87 : Sig := (0x4ca2, 0x1c2)
def s88 : Sig := (0x5818, 0xfffffffffffffccf)
def s89 : Sig := (0x583e, 0xfffffffffffffccf)
def s90 : Sig := (0x5898, 0xfffffffffffffccf)
def s91 : Sig := (0x5918, 0xfffffffffffffccf)
def s92 : Sig := (0x5c18, 0xfffffffffffffccf)
def s93 : Sig := (0x5d98, 0xfffffffffffffecf)
def s94 : Sig := (0x6822, 0xfffffffffffffdd3)
def s95 : Sig := (0x6ea2, 0xffffffffffffffd3)
def s96 : Sig := (0x7048, 0xfffffffffffffd75)
def s97 : Sig := (0x7800, 0x400)
def s98 : Sig := (0x7818, 0xfffffffffffffccf)
def s99 : Sig := (0x7826, 0xfffffffffffffdff)
def s100 : Sig := (0x7836, 0x48a)
def s101 : Sig := (0x7858, 0xfffffffffffffdff)
def s102 : Sig := (0x787e, 0xfffffffffffffdff)
def s103 : Sig := (0x78fe, 0xfffffffffffffdff)
def s104 : Sig := (0x7f80, 0x600)
def s105 : Sig := (0x7fb6, 0x68a)
def s106 : Sig := (0x7ffe, 0xffffffffffffffff)
def s107 : Sig := (0x8000, 0x0)
def s108 : Sig := (0x8000, 0xfffffffffffffe01)
def s109 : Sig := (0x8006, 0xfffffffffffff83f)
def s110 : Sig := (0x807e, 0xfffffffffffff9ff)
def s111 : Sig := (0x8180, 0x200)
def s112 : Sig := (0x8180, 0xfffffffffffffa0f)
def s113 : Sig := (0x8280, 0x200)
def s114 : Sig := (0x8380, 0x200)
def s115 : Sig := (0x8380, 0xfffffffffffffa0f)
def s116 : Sig := (0x8386, 0xfffffffffffffa3f)
def s117 : Sig := (0x8580, 0x200)
def s118 : Sig := (0x8598, 0xfffffffffffffacf)
def s119 : Sig := (0x8680, 0x200)
def s120 : Sig := (0x8700, 0x200)
def s121 : Sig := (0x8780, 0x200)
def s122 : Sig := (0x87fe, 0xfffffffffffffbff)
def s123 : Sig := (0x8880, 0xfffffffffffffe03)
def s124 : Sig := (0x8886, 0xfffffffffffff83f)
def s125 : Sig := (0x8886, 0xfffffffffffffe3f)
def s126 : Sig := (0x8b86, 0x20a)
def s127 : Sig := (0x8b86, 0xfffffffffffffe3f)
def s128 : Sig := (0x8d90, 0x28a)
def s129 : Sig := (0x8f36, 0x28a)
def s130 : Sig := (0x9100, 0xfffffffffffffe05)
def s131 : Sig := (0x9800, 0x400)
def s132 : Sig := (0x9980, 0x600)
def s133 : Sig := (0x9980, 0xfffffffffffffe0f)
def s134 : Sig := (0x9984, 0xfffffffffffffe2f)
def s135 : Sig := (0x9986, 0xfffffffffffffe0f)
def s136 : Sig := (0x9986, 0xfffffffffffffe3f)
def s137 : Sig := (0x9990, 0xfffffffffffffe8f)
def s138 : Sig := (0x9998, 0xfffffffffffffe0f)
def s139 : Sig := (0x99fe, 0xffffffffffffffff)
def s140 : Sig := (0x9b80, 0x600)
def s141 : Sig := (0x9b80, 0xfffffffffffffe0f)
def s142 : Sig := (0x9b86, 0x22e)
def s143 : Sig := (0x9b86, 0xfffffffffffffe3f)
def s144 : Sig := (0x9d80, 0xfffffffffffffe0f)
def s145 : Sig := (0x9d98, 0xfffffffffffffecf)
def s146 : Sig := (0x9ffe, 0xffffffffffffffff)
def s147 : Sig := (0xaa80, 0x600)
def s148 : Sig := (0xaa82, 0xfffffffffffffe13)
def s149 : Sig := (0xaa86, 0xfffffffffffffe3f)
def s150 : Sig := (0xab80, 0x600)
def s151 : Sig := (0xab86, 0xfffffffffffffe3f)
def s152 : Sig := (0xaea2, 0xffffffffffffffd3)
def s153 : Sig := (0xb300, 0xfffffffffffffe35)
def s154 : Sig := (0xb800, 0x400)
def s155 : Sig := (0xb806, 0xfffffffffffffc3f)
def s156 : Sig := (0xb980, 0xfffffffffffffe0f)
def s157 : Sig := (0xb986, 0xfffffffffffffe3f)
def s158 : Sig := (0xbb80, 0x600)
def s159 : Sig := (0xbb80, 0xfffffffffffffe3f)
def s160 : Sig := (0xbb84, 0x62c)
def s161 : Sig := (0xbb86, 0xfffffffffffffe3f)
def s162 : Sig := (0xbbfe, 0xffffffffffffffff)
def s163 : Sig := (0xbd80, 0x600)
def s164 : Sig := (0xbe80, 0x600)
def s165 : Sig := (0xbf80, 0x600)
def s166 : Sig := (0xbffe, 0xffffffffffffffff)
def s167 : Sig := (0xc400, 0xfffffffffffffe41)
def s168 : Sig := (0xc418, 0xfffffffffffff8cf)
def s169 : Sig := (0xc598, 0x2c0)
def s170 : Sig := (0xc6a0, 0x3c0)
def s171 : Sig := (0xcc80, 0x600)
def s172 : Sig := (0xcc80, 0xfffffffffffffec3)
def s173 : Sig := (0xcca0, 0xffffffffffffffc3)
def s174 : Sig := (0xcca2, 0xffffffffffffffd3)
def s175 : Sig := (0xccfe, 0xffffffffffffffff)
def s176 : Sig := (0xd508, 0xfffffffffffffe45)
def s177 : Sig := (0xd518, 0xfffffffffffffecf)
def s178 : Sig := (0xd800, 0x400)
def s179 : Sig := (0xd818, 0xfffffffffffffccf)
def s180 : Sig := (0xd890, 0x48a)
def s181 : Sig := (0xdc18, 0xfffffffffffffccf)
def s182 : Sig := (0xdd18, 0xfffffffffffffecf)
def s183 : Sig := (0xdd80, 0x600)
def s184 : Sig := (0xdd98, 0x6c0)
def s185 : Sig := (0xdd98, 0xfffffffffffffecf)
def s186 : Sig := (0xddfe, 0xffffffffffffffff)
def s187 : Sig := (0xe000, 0x400)
def s188 : Sig := (0xe600, 0xffffffffffffff51)
def s189 : Sig := (0xe800, 0x400)
def s190 : Sig := (0xe8a2, 0x482)
def s191 : Sig := (0xeca0, 0xffffffffffffffc3)
def s192 : Sig := (0xeca2, 0xffffffffffffffd3)
def s193 : Sig := (0xee80, 0x600)
def s194 : Sig := (0xeea0, 0x7c0)
def s195 : Sig := (0xeea2, 0xffffffffffffffd3)
def s196 : Sig := (0xf000, 0x400)
def s197 : Sig := (0xf700, 0x600)
def s198 : Sig := (0xf748, 0xffffffffffffff75)
def s199 : Sig := (0xf758, 0xffffffffffffff7d)
def s200 : Sig := (0xf758, 0xffffffffffffffff)
def s201 : Sig := (0xfdfe, 0xffffffffffffffff)
def s202 : Sig := (0xff80, 0x600)
def s203 : Sig := (0xff9e, 0xfffffffffffffeff)
def s204 : Sig := (0xffa6, 0xffffffffffffffff)
def s205 : Sig := (0xffd8, 0xffffffffffffffff)
def bucketTier1 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def bucketTier2 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def bucketTier3 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def b4_8 : List (List Sig) := [
  [s3, s26, s88, s148, s198],
  [s3, s27, s88, s148, s198]]
def bucketTier4 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], b4_8, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def b5_3 : List (List Sig) := [
  [s21, s41, s102, s130, s195],
  [s22, s41, s102, s130, s195],
  [s22, s43, s101, s130, s195]]
def b5_4 : List (List Sig) := [
  [s5, s10, s60, s185, s195, s198]]
def b5_5 : List (List Sig) := [
  [s5, s81, s161, s185, s195, s198],
  [s22, s32, s102, s108, s185, s198]]
def b5_6 : List (List Sig) := [
  [s5, s22, s94, s123, s185, s198],
  [s5, s62, s80, s185, s195, s198],
  [s5, s62, s161, s185, s195, s198],
  [s5, s80, s171, s185, s195, s198],
  [s22, s32, s88, s102, s123, s198]]
def b5_14 : List (List Sig) := [
  [s0, s5, s63, s93, s195, s198],
  [s0, s5, s63, s185, s195, s198],
  [s0, s5, s95, s133, s185, s198],
  [s5, s22, s72, s185, s195, s200]]
def b5_15 : List (List Sig) := [
  [s5, s12, s61, s185, s195, s198],
  [s5, s22, s72, s174, s185, s198],
  [s5, s22, s72, s176, s195, s205],
  [s5, s22, s72, s177, s195, s198],
  [s5, s22, s101, s161, s176, s195],
  [s5, s46, s80, s185, s195, s198],
  [s5, s46, s93, s161, s195, s198],
  [s5, s46, s95, s161, s185, s198],
  [s5, s55, s76, s185, s195, s198],
  [s5, s55, s78, s185, s195, s198],
  [s5, s65, s80, s185, s195, s198],
  [s5, s65, s161, s185, s195, s198],
  [s5, s80, s175, s185, s195, s198],
  [s5, s124, s161, s185, s195, s198],
  [s21, s41, s72, s102, s176, s195],
  [s22, s41, s72, s102, s176, s195]]
def b5_18 : List (List Sig) := [
  [s3, s26, s88, s161, s195, s198],
  [s3, s26, s102, s148, s185, s198],
  [s3, s27, s88, s161, s195, s198],
  [s3, s27, s99, s148, s185, s198],
  [s3, s27, s102, s148, s185, s198],
  [s5, s80, s168, s185, s195, s198]]
def b5_23 : List (List Sig) := [
  [s22, s43, s101, s102, s130, s195]]
def b5_24 : List (List Sig) := [
  [s3, s39, s102, s123, s185, s198],
  [s3, s43, s102, s123, s185, s198],
  [s5, s39, s102, s123, s185, s198]]
def b5_25 : List (List Sig) := [
  [s5, s22, s72, s173, s185, s198]]
def b5_29 : List (List Sig) := [
  [s0, s5, s93, s153, s195, s198],
  [s79, s80, s183, s185, s195, s198],
  [s80, s183, s185, s193, s195, s198]]
def bucketTier5 : List (List (List Sig)) := [[], [], [], b5_3, b5_4, b5_5, b5_6, [], [], [], [], [], [], [], b5_14, b5_15, [], [], b5_18, [], [], [], [], b5_23, b5_24, b5_25, [], [], [], b5_29, []]

def b6_0 : List (List Sig) := [
  [s21, s41, s102, s133, s195, s198],
  [s22, s41, s102, s133, s195, s198],
  [s22, s43, s101, s133, s195, s198]]
def b6_1 : List (List Sig) := [
  [s5, s22, s45, s72, s185, s195, s198],
  [s22, s32, s102, s148, s176, s185, s198]]
def b6_2 : List (List Sig) := [
  [s22, s43, s102, s133, s172, s188, s198]]
def b6_3 : List (List Sig) := [
  [s5, s43, s102, s123, s185, s198, s204]]
def b6_4 : List (List Sig) := [
  [s5, s22, s87, s102, s185, s195, s198],
  [s5, s22, s102, s134, s185, s195, s198],
  [s5, s22, s102, s161, s173, s185, s198],
  [s22, s27, s68, s102, s153, s195],
  [s22, s43, s72, s102, s173, s185, s198],
  [s22, s43, s86, s96, s102, s185, s195]]
def b6_5 : List (List Sig) := [
  [s5, s22, s94, s133, s185, s195, s198],
  [s5, s66, s185, s195, s198],
  [s5, s70, s185, s195, s198],
  [s5, s80, s93, s195, s198],
  [s5, s80, s95, s185, s198],
  [s5, s80, s185, s195, s198],
  [s5, s105, s161, s185, s195, s198],
  [s15, s102, s161, s185, s187, s195, s198],
  [s21, s41, s102, s161, s176, s195],
  [s22, s32, s88, s102, s133, s195, s198],
  [s22, s41, s102, s161, s176, s195],
  [s22, s43, s101, s161, s176, s195],
  [s22, s43, s102, s132, s185, s195, s198]]
def b6_6 : List (List Sig) := [
  [s5, s79, s80, s185, s195, s198],
  [s5, s79, s161, s185, s195, s198],
  [s5, s80, s104, s185, s195, s198],
  [s5, s80, s158, s185, s195, s198],
  [s5, s80, s183, s185, s195, s198],
  [s5, s80, s185, s193, s195, s198],
  [s5, s82, s161, s185, s195, s198],
  [s5, s104, s161, s185, s195, s198],
  [s5, s111, s131, s161, s185, s195, s198]]
def b6_7 : List (List Sig) := [
  [s0, s104, s161, s185, s195, s198],
  [s22, s72, s183, s185, s195, s198],
  [s22, s72, s185, s193, s195, s198]]
def b6_8 : List (List Sig) := [
  [s106, s158, s161, s183, s185, s195, s198]]
def b6_9 : List (List Sig) := [
  [s22, s32, s102, s130, s185, s195, s198]]
def b6_10 : List (List Sig) := [
  [s5, s22, s88, s148, s185, s195, s198],
  [s22, s32, s88, s102, s148, s185, s198]]
def b6_11 : List (List Sig) := [
  [s5, s80, s172, s185, s195, s198],
  [s22, s43, s89, s102, s153, s185, s195]]
def b6_13 : List (List Sig) := [
  [s5, s22, s27, s102, s133, s195, s198],
  [s22, s43, s102, s130, s195, s205]]
def b6_14 : List (List Sig) := [
  [s3, s39, s102, s148, s185, s198],
  [s3, s43, s102, s148, s185, s198],
  [s4, s5, s22, s72, s185, s195, s198],
  [s5, s7, s22, s72, s185, s195, s198],
  [s5, s7, s22, s96, s161, s185, s195],
  [s5, s9, s72, s185, s195, s198],
  [s5, s10, s102, s134, s185, s195, s198],
  [s5, s22, s47, s72, s185, s195, s198],
  [s5, s22, s47, s96, s161, s185, s195],
  [s5, s22, s88, s133, s195, s198],
  [s5, s22, s170, s185, s195, s198],
  [s5, s39, s102, s148, s185, s198],
  [s5, s110, s161, s185, s195, s198],
  [s10, s43, s60, s102, s185, s195, s198],
  [s39, s43, s102, s123, s185, s198]]
def b6_15 : List (List Sig) := [
  [s0, s5, s80, s185, s195, s198],
  [s0, s5, s93, s161, s195, s198],
  [s0, s5, s95, s161, s185, s198],
  [s5, s22, s72, s185, s195, s198],
  [s5, s22, s74, s185, s195, s198],
  [s5, s22, s76, s185, s195, s198],
  [s5, s22, s77, s185, s195, s198],
  [s5, s63, s80, s185, s195, s198],
  [s5, s63, s161, s185, s195, s198],
  [s5, s80, s133, s185, s195, s198],
  [s5, s109, s161, s185, s195, s198],
  [s8, s22, s72, s185, s195, s198],
  [s22, s43, s102, s108, s185, s195, s198],
  [s39, s102, s123, s185, s198]]
def b6_16 : List (List Sig) := [
  [s5, s22, s72, s183, s185, s195, s198],
  [s5, s22, s102, s123, s185, s195, s198],
  [s5, s104, s133, s161, s185, s195, s198],
  [s5, s106, s132, s161, s185, s195, s198],
  [s22, s43, s88, s102, s123, s195, s198],
  [s22, s43, s94, s102, s123, s185, s198],
  [s43, s102, s133, s153, s172, s188]]
def b6_17 : List (List Sig) := [
  [s5, s80, s161, s183, s185, s195, s198]]
def b6_18 : List (List Sig) := [
  [s5, s22, s27, s72, s185, s195, s198],
  [s8, s27, s88, s161, s195, s198]]
def b6_19 : List (List Sig) := [
  [s5, s22, s48, s72, s185, s195, s198],
  [s5, s22, s169, s185, s195, s198],
  [s5, s43, s102, s133, s161, s195, s200]]
def b6_20 : List (List Sig) := [
  [s22, s43, s101, s102, s133, s195, s198]]
def b6_21 : List (List Sig) := [
  [s5, s22, s72, s172, s185, s195, s198],
  [s22, s32, s72, s102, s172, s185, s198]]
def b6_22 : List (List Sig) := [
  [s22, s28, s102, s153, s185, s195],
  [s22, s32, s102, s133, s185, s188, s198]]
def b6_23 : List (List Sig) := [
  [s3, s39, s102, s133, s185, s195, s198],
  [s3, s43, s102, s133, s185, s195, s198],
  [s5, s39, s102, s133, s185, s195, s198]]
def b6_24 : List (List Sig) := [
  [s0, s5, s106, s133, s185, s195, s198],
  [s5, s9, s59, s161, s185, s195, s198],
  [s5, s22, s102, s161, s185, s195, s200],
  [s5, s43, s102, s125, s185, s195, s198],
  [s5, s50, s80, s185, s195],
  [s5, s50, s93, s161, s195],
  [s8, s27, s102, s133, s161, s195, s198],
  [s22, s43, s88, s102, s133, s195, s198],
  [s22, s43, s88, s102, s135, s195, s198],
  [s22, s43, s90, s102, s133, s195, s198],
  [s22, s43, s91, s102, s133, s195, s198],
  [s22, s43, s92, s102, s133, s195, s198],
  [s22, s43, s98, s102, s133, s195, s198]]
def b6_25 : List (List Sig) := [
  [s5, s12, s102, s136, s185, s195, s198],
  [s5, s22, s72, s133, s185, s195, s198],
  [s5, s22, s72, s185, s186, s195, s198],
  [s5, s22, s72, s185, s195, s198, s205],
  [s5, s22, s101, s161, s185, s195, s198],
  [s5, s22, s102, s136, s185, s195, s198],
  [s5, s22, s102, s161, s174, s185, s198],
  [s5, s22, s102, s161, s176, s195, s205],
  [s5, s22, s102, s161, s177, s195, s198],
  [s5, s22, s119, s133, s185, s195, s198],
  [s5, s46, s106, s161, s185, s195, s198],
  [s5, s50, s104, s161, s185, s195],
  [s5, s106, s139, s161, s185, s195, s198],
  [s8, s55, s102, s161, s185, s195, s198],
  [s8, s69, s102, s161, s185, s195, s198],
  [s21, s41, s72, s102, s185, s195, s198],
  [s22, s41, s72, s102, s185, s195, s198],
  [s22, s43, s72, s102, s176, s195, s205],
  [s22, s43, s88, s120, s133, s195, s198],
  [s22, s43, s101, s102, s161, s176, s195],
  [s43, s55, s76, s102, s185, s195, s198],
  [s43, s55, s78, s102, s185, s195, s198]]
def b6_26 : List (List Sig) := [
  [s5, s55, s117, s161, s185, s195, s198],
  [s5, s55, s120, s161, s185, s195, s198]]
def b6_27 : List (List Sig) := [
  [s5, s22, s94, s148, s185, s198],
  [s22, s32, s72, s94, s185, s198],
  [s22, s32, s102, s123, s185, s198],
  [s22, s32, s102, s133, s172, s198]]
def b6_28 : List (List Sig) := [
  [s0, s5, s27, s88, s161, s195, s198],
  [s3, s26, s102, s161, s185, s195, s198],
  [s3, s27, s99, s161, s185, s195, s198],
  [s3, s27, s102, s161, s185, s195, s198],
  [s5, s22, s73, s185, s195, s198]]
def b6_29 : List (List Sig) := [
  [s0, s5, s93, s161, s185, s195, s198],
  [s5, s22, s88, s161, s185, s195, s198],
  [s5, s22, s89, s161, s185, s195, s198],
  [s5, s22, s90, s161, s185, s195, s198],
  [s5, s22, s91, s161, s185, s195, s198],
  [s5, s22, s92, s161, s185, s195, s198],
  [s5, s22, s98, s161, s185, s195, s198],
  [s8, s22, s88, s161, s185, s195, s198],
  [s104, s158, s161, s185, s195, s198]]
def b6_30 : List (List Sig) := [
  [s5, s22, s72, s176, s185, s195, s198]]
def bucketTier6 : List (List (List Sig)) := [b6_0, b6_1, b6_2, b6_3, b6_4, b6_5, b6_6, b6_7, b6_8, b6_9, b6_10, b6_11, [], b6_13, b6_14, b6_15, b6_16, b6_17, b6_18, b6_19, b6_20, b6_21, b6_22, b6_23, b6_24, b6_25, b6_26, b6_27, b6_28, b6_29, b6_30]

def b7_0 : List (List Sig) := [
  [s5, s22, s102, s161, s172, s185, s195, s198],
  [s5, s43, s114, s161, s172, s185, s195, s198],
  [s22, s27, s102, s148, s185, s195, s198],
  [s22, s43, s72, s102, s172, s185, s195, s198],
  [s22, s102, s161, s185, s190, s195, s198],
  [s43, s102, s128, s133, s161, s195, s198],
  [s43, s102, s133, s153, s172, s195, s198]]
def b7_1 : List (List Sig) := [
  [s9, s43, s102, s161, s185, s188, s195, s198],
  [s22, s27, s68, s102, s161, s195, s198],
  [s22, s43, s102, s133, s185, s188, s195, s198]]
def b7_2 : List (List Sig) := [
  [s0, s5, s43, s102, s133, s185, s195, s198],
  [s5, s43, s102, s160, s185, s195, s198],
  [s22, s27, s102, s153, s185, s195, s198]]
def b7_3 : List (List Sig) := [
  [s2, s38, s102, s161, s185, s195, s198],
  [s5, s9, s102, s133, s161, s185, s195, s198],
  [s5, s43, s46, s102, s161, s185, s195, s198],
  [s5, s43, s64, s102, s161, s185, s195, s198],
  [s5, s43, s102, s133, s161, s185, s195, s198],
  [s5, s43, s102, s134, s185, s195, s198],
  [s5, s43, s102, s135, s161, s185, s195, s198],
  [s5, s43, s102, s139, s161, s185, s195, s198],
  [s5, s50, s106, s161, s185, s195],
  [s8, s43, s96, s102, s161, s185, s195],
  [s8, s43, s102, s133, s161, s185, s195, s198],
  [s9, s43, s59, s102, s161, s185, s195, s198],
  [s9, s43, s72, s102, s133, s185, s195, s198],
  [s22, s27, s43, s102, s133, s195, s198],
  [s43, s50, s80, s102, s185, s195],
  [s43, s50, s93, s102, s161, s195]]
def b7_4 : List (List Sig) := [
  [s5, s22, s102, s133, s161, s185, s195, s198],
  [s5, s22, s102, s161, s185, s186, s195, s198],
  [s5, s22, s102, s161, s185, s195, s198, s205],
  [s5, s43, s80, s185, s195, s198],
  [s5, s43, s102, s136, s161, s185, s195, s198],
  [s5, s43, s111, s133, s161, s185, s195, s198],
  [s5, s43, s114, s133, s161, s185, s195, s198],
  [s7, s43, s102, s161, s185, s195, s197],
  [s10, s43, s102, s134, s185, s195, s198],
  [s19, s22, s43, s102, s133, s185, s195, s198],
  [s22, s34, s43, s102, s133, s185, s195, s198],
  [s22, s43, s72, s102, s133, s185, s195, s198],
  [s22, s43, s72, s102, s185, s195, s198, s205],
  [s22, s43, s75, s185, s195, s198],
  [s22, s43, s88, s102, s133, s161, s195, s198],
  [s22, s43, s101, s102, s161, s185, s195, s198],
  [s22, s43, s102, s111, s133, s185, s195, s198],
  [s22, s43, s102, s114, s133, s185, s195, s198],
  [s22, s43, s102, s117, s133, s185, s195, s198],
  [s22, s43, s102, s119, s133, s185, s195, s198],
  [s22, s43, s102, s145, s195, s198],
  [s22, s43, s102, s152, s185, s198],
  [s39, s43, s102, s148, s185, s198]]
def b7_5 : List (List Sig) := [
  [s5, s43, s104, s161, s185, s195, s198],
  [s5, s80, s185, s195, s198],
  [s5, s107, s161, s185, s195, s198],
  [s8, s102, s154, s161, s185, s195, s198],
  [s8, s102, s161, s178, s185, s195, s198],
  [s8, s102, s161, s185, s195, s196, s198],
  [s22, s43, s102, s158, s185, s195, s198],
  [s39, s102, s148, s185, s198],
  [s43, s55, s102, s117, s161, s185, s195, s198],
  [s43, s55, s102, s120, s161, s185, s195, s198]]
def b7_6 : List (List Sig) := [
  [s4, s5, s43, s102, s153, s161, s185, s195],
  [s5, s7, s43, s102, s153, s161, s185, s195],
  [s5, s22, s94, s161, s185, s195, s198],
  [s5, s22, s102, s148, s185, s195, s198],
  [s5, s34, s97, s161, s185, s195, s198],
  [s5, s104, s161, s185, s195, s198],
  [s5, s114, s154, s161, s185, s195, s198],
  [s5, s114, s161, s178, s185, s195, s198],
  [s5, s114, s161, s185, s189, s195, s198],
  [s22, s32, s72, s102, s185, s195, s198],
  [s22, s43, s94, s102, s148, s185, s198],
  [s22, s43, s102, s123, s185, s195, s198],
  [s22, s43, s102, s133, s172, s195, s198]]
def b7_7 : List (List Sig) := [
  [s0, s1, s43, s102, s161, s185, s195, s198],
  [s0, s5, s27, s102, s161, s185, s195, s198],
  [s5, s23, s102, s161, s185, s195, s198],
  [s7, s43, s71, s102, s161, s185, s195],
  [s7, s43, s72, s102, s153, s185, s195],
  [s22, s43, s73, s102, s185, s195, s198],
  [s104, s106, s161, s185, s195, s198]]
def b7_8 : List (List Sig) := [
  [s22, s43, s88, s102, s161, s185, s195, s198],
  [s22, s43, s89, s102, s161, s185, s195, s198],
  [s22, s43, s90, s102, s161, s185, s195, s198],
  [s22, s43, s91, s102, s161, s185, s195, s198],
  [s22, s43, s92, s102, s161, s185, s195, s198],
  [s22, s43, s98, s102, s161, s185, s195, s198],
  [s22, s43, s102, s161, s179, s185, s195, s198],
  [s22, s43, s102, s161, s181, s185, s195, s198]]
def b7_9 : List (List Sig) := [
  [s5, s22, s102, s161, s176, s185, s195, s198],
  [s22, s34, s43, s88, s161, s185, s195, s198],
  [s22, s43, s72, s102, s176, s185, s195, s198],
  [s22, s43, s88, s120, s161, s185, s195, s198]]
def b7_10 : List (List Sig) := [
  [s22, s43, s102, s133, s195, s198, s205]]
def b7_11 : List (List Sig) := [
  [s5, s22, s45, s102, s161, s185, s195, s198],
  [s5, s43, s126, s161, s185, s195, s198],
  [s15, s43, s102, s161, s185, s188, s195, s198],
  [s22, s32, s102, s161, s176, s185, s195, s198],
  [s22, s43, s45, s72, s102, s185, s195, s198],
  [s22, s43, s45, s96, s102, s161, s185, s195],
  [s22, s43, s102, s148, s176, s185, s195, s198]]
def b7_12 : List (List Sig) := [
  [s5, s43, s49, s102, s161, s185, s195],
  [s5, s43, s50, s102, s161, s185, s195],
  [s7, s43, s44, s102, s161, s185, s195]]
def b7_13 : List (List Sig) := [
  [s5, s7, s43, s96, s161, s185, s195],
  [s5, s22, s85, s102, s185, s195, s198],
  [s22, s43, s102, s137, s195, s198],
  [s39, s43, s102, s133, s185, s195, s198]]
def b7_14 : List (List Sig) := [
  [s5, s22, s43, s72, s185, s195, s198],
  [s5, s43, s102, s134, s161, s185, s195, s198],
  [s9, s43, s102, s161, s185, s195, s198],
  [s11, s43, s102, s161, s185, s195, s198],
  [s16, s43, s102, s161, s185, s195, s198],
  [s20, s43, s102, s161, s185, s195, s198],
  [s22, s30, s102, s161, s185, s195, s198],
  [s22, s43, s102, s133, s185, s195, s198],
  [s22, s43, s102, s135, s185, s195, s198],
  [s22, s43, s102, s138, s185, s195, s198],
  [s22, s43, s102, s141, s185, s195, s198],
  [s22, s43, s102, s144, s185, s195, s198],
  [s22, s43, s102, s156, s185, s195, s198],
  [s35, s43, s102, s161, s185, s195, s198],
  [s36, s43, s102, s133, s185, s195, s198],
  [s39, s102, s133, s185, s195, s198],
  [s43, s52, s102, s161, s185, s195, s198],
  [s43, s53, s102, s161, s185, s195, s198],
  [s43, s55, s102, s133, s185, s195, s198],
  [s43, s56, s102, s133, s161, s195, s198],
  [s43, s102, s112, s161, s185, s195, s198],
  [s43, s102, s115, s161, s185, s195, s198],
  [s43, s102, s116, s133, s185, s195, s198]]
def b7_15 : List (List Sig) := [
  [s5, s22, s72, s185, s195, s198],
  [s5, s22, s102, s158, s185, s195, s198],
  [s5, s80, s106, s185, s195, s198],
  [s5, s83, s161, s185, s195, s198],
  [s5, s106, s161, s185, s195, s198],
  [s12, s31, s102, s161, s185, s195, s198],
  [s12, s43, s102, s157, s185, s195, s198],
  [s12, s43, s102, s161, s185, s195, s198],
  [s16, s102, s161, s185, s195, s198],
  [s21, s41, s102, s161, s185, s195, s198],
  [s22, s31, s102, s161, s185, s195, s198],
  [s22, s41, s102, s161, s185, s195, s198],
  [s22, s43, s94, s102, s133, s185, s195, s198],
  [s22, s43, s101, s161, s185, s195, s198],
  [s22, s43, s102, s157, s185, s195, s198],
  [s22, s43, s102, s161, s176, s195, s205],
  [s22, s43, s102, s161, s182, s195, s198],
  [s22, s43, s102, s161, s185, s192, s198],
  [s42, s43, s102, s161, s185, s188, s195, s198],
  [s43, s66, s102, s185, s195, s198],
  [s43, s70, s102, s185, s195, s198],
  [s43, s80, s93, s102, s195, s198],
  [s43, s80, s95, s102, s185, s198],
  [s43, s80, s102, s185, s195, s198],
  [s43, s102, s127, s185, s195, s198],
  [s43, s102, s142, s161, s185, s195, s198]]
def b7_16 : List (List Sig) := [
  [s5, s80, s161, s185, s195, s198],
  [s5, s104, s106, s161, s185, s195, s198],
  [s5, s106, s158, s161, s185, s195, s198],
  [s22, s43, s102, s161, s183, s185, s195, s198],
  [s34, s43, s80, s185, s195, s198],
  [s43, s102, s104, s161, s185, s195, s198],
  [s43, s102, s111, s131, s161, s185, s195, s198],
  [s43, s102, s132, s161, s185, s195, s198],
  [s43, s102, s140, s161, s185, s195, s198],
  [s43, s102, s147, s161, s185, s195, s198],
  [s43, s102, s150, s161, s185, s195, s198],
  [s43, s102, s158, s161, s185, s195, s198],
  [s43, s102, s161, s163, s185, s195, s198],
  [s43, s102, s161, s164, s185, s195, s198],
  [s43, s102, s161, s165, s185, s195, s198],
  [s43, s102, s161, s185, s195, s198, s202]]
def b7_17 : List (List Sig) := [
  [s5, s43, s45, s102, s161, s185, s188, s195],
  [s5, s43, s102, s133, s153, s185, s195, s198],
  [s7, s22, s43, s102, s153, s185, s195],
  [s14, s43, s94, s102, s161, s185, s198],
  [s22, s32, s102, s148, s185, s198],
  [s22, s43, s102, s161, s167, s185, s195, s198],
  [s22, s43, s102, s161, s172, s185, s188, s198],
  [s22, s102, s161, s183, s185, s195, s198],
  [s22, s102, s161, s185, s193, s195, s198],
  [s34, s43, s104, s161, s185, s195, s198],
  [s43, s102, s158, s161, s183, s185, s195, s198],
  [s43, s114, s161, s183, s185, s195, s198],
  [s43, s114, s161, s185, s193, s195, s198]]
def b7_18 : List (List Sig) := [
  [s5, s22, s84, s102, s185, s195, s198],
  [s8, s43, s102, s153, s161, s185, s195, s198],
  [s22, s43, s85, s102, s172, s185, s198],
  [s40, s43, s102, s153, s161, s185, s195]]
def b7_19 : List (List Sig) := [
  [s5, s43, s47, s102, s133, s161, s195, s198],
  [s5, s43, s102, s161, s185, s195, s199],
  [s22, s27, s102, s161, s185, s195, s198],
  [s22, s28, s102, s161, s185, s195, s198],
  [s22, s37, s102, s161, s185, s195, s198],
  [s22, s43, s102, s117, s153, s185, s195, s198],
  [s22, s56, s102, s161, s185, s195, s198],
  [s22, s58, s102, s161, s185, s195, s198],
  [s22, s102, s118, s161, s185, s195, s198]]
def b7_20 : List (List Sig) := [
  [s22, s32, s88, s102, s161, s185, s195, s198],
  [s22, s43, s88, s102, s148, s185, s195, s198],
  [s22, s43, s102, s161, s184, s185, s195, s198]]
def b7_21 : List (List Sig) := [
  [s22, s27, s67, s102, s161, s195, s198],
  [s43, s80, s102, s172, s185, s195, s198]]
def b7_22 : List (List Sig) := [
  [s22, s43, s48, s102, s153, s185, s195],
  [s22, s43, s88, s102, s153, s185, s195, s198]]
def b7_23 : List (List Sig) := [
  [s5, s22, s43, s102, s133, s185, s195, s198],
  [s5, s43, s102, s161, s185, s195, s200]]
def b7_24 : List (List Sig) := [
  [s0, s22, s43, s102, s133, s185, s195, s198],
  [s3, s39, s102, s161, s185, s195, s198],
  [s3, s43, s102, s161, s185, s195, s198],
  [s4, s5, s22, s102, s161, s185, s195, s198],
  [s5, s7, s22, s102, s161, s185, s195, s198],
  [s5, s7, s43, s72, s161, s185, s195, s198],
  [s5, s7, s102, s161, s185, s195, s196],
  [s5, s9, s102, s161, s185, s195, s198],
  [s5, s22, s47, s102, s161, s185, s195, s198],
  [s5, s22, s102, s133, s185, s195, s198],
  [s5, s25, s102, s161, s185, s195, s198],
  [s5, s39, s102, s161, s185, s195, s198],
  [s5, s43, s80, s102, s185, s195, s198],
  [s5, s43, s102, s136, s185, s195, s198],
  [s5, s43, s102, s143, s185, s195, s198],
  [s5, s43, s102, s148, s185, s198, s204],
  [s5, s43, s102, s149, s185, s195, s198],
  [s5, s43, s102, s151, s185, s195, s198],
  [s5, s43, s102, s159, s185, s195, s198],
  [s5, s43, s102, s161, s185, s195, s198],
  [s5, s43, s103, s161, s185, s195, s198],
  [s5, s43, s128, s161, s185, s195, s198],
  [s7, s22, s43, s72, s102, s185, s195, s198],
  [s7, s22, s43, s96, s102, s161, s185, s195],
  [s8, s43, s102, s161, s185, s195, s198],
  [s9, s43, s72, s102, s185, s195, s198],
  [s15, s43, s102, s161, s185, s195, s198],
  [s18, s43, s102, s161, s185, s195, s198],
  [s22, s43, s47, s72, s102, s185, s195, s198],
  [s22, s43, s47, s96, s102, s161, s185, s195],
  [s22, s43, s88, s102, s133, s195, s198],
  [s22, s43, s102, s161, s185, s194, s198],
  [s22, s43, s102, s170, s185, s195, s198],
  [s43, s51, s102, s161, s185, s195, s198],
  [s43, s102, s129, s161, s185, s195]]
def b7_25 : List (List Sig) := [
  [s0, s5, s106, s161, s185, s195, s198],
  [s5, s22, s102, s154, s185, s195, s198],
  [s5, s22, s102, s161, s185, s195, s198],
  [s5, s24, s102, s161, s185, s195, s198],
  [s5, s36, s102, s161, s185, s195, s198],
  [s5, s43, s76, s161, s185, s195, s198],
  [s5, s43, s77, s161, s185, s195, s198],
  [s5, s43, s102, s132, s161, s185, s195, s198],
  [s5, s43, s111, s161, s185, s195, s198],
  [s5, s43, s113, s161, s185, s195, s198],
  [s5, s43, s114, s161, s185, s195, s198],
  [s5, s43, s121, s161, s185, s195, s198],
  [s5, s106, s133, s161, s185, s195, s198],
  [s7, s43, s72, s96, s161, s185, s195],
  [s8, s22, s102, s161, s185, s195, s198],
  [s8, s33, s102, s161, s185, s195, s198],
  [s8, s43, s72, s161, s185, s195, s198],
  [s8, s43, s114, s161, s185, s195, s198],
  [s8, s43, s117, s161, s185, s195, s198],
  [s10, s43, s102, s161, s185, s195, s198],
  [s22, s43, s72, s102, s185, s195, s198],
  [s22, s43, s74, s102, s185, s195, s198],
  [s22, s43, s76, s102, s185, s195, s198],
  [s22, s43, s77, s102, s185, s195, s198],
  [s22, s43, s86, s102, s185, s195, s198],
  [s22, s43, s87, s102, s185, s195, s198],
  [s22, s43, s102, s134, s185, s195, s198],
  [s22, s43, s102, s155, s185, s195, s198],
  [s22, s43, s102, s161, s173, s185, s198],
  [s22, s43, s102, s161, s185, s191, s198],
  [s43, s63, s80, s102, s185, s195, s198],
  [s43, s63, s102, s161, s185, s195, s198],
  [s43, s80, s102, s133, s185, s195, s198],
  [s43, s102, s123, s185, s198, s204]]
def b7_26 : List (List Sig) := [
  [s0, s43, s102, s161, s183, s185, s195, s198],
  [s5, s22, s72, s161, s185, s195, s198],
  [s5, s22, s102, s161, s183, s185, s195, s198],
  [s5, s22, s114, s161, s185, s195, s198],
  [s5, s22, s117, s161, s185, s195, s198],
  [s5, s22, s119, s161, s185, s195, s198],
  [s5, s43, s102, s123, s161, s185, s195, s198],
  [s9, s32, s102, s161, s185, s195, s198],
  [s9, s97, s102, s161, s185, s195, s198],
  [s9, s102, s161, s185, s189, s195, s198],
  [s22, s32, s102, s133, s185, s195, s198],
  [s22, s34, s43, s72, s185, s195, s198],
  [s22, s43, s72, s117, s185, s195, s198],
  [s22, s43, s72, s119, s185, s195, s198],
  [s22, s97, s102, s133, s185, s195, s198],
  [s22, s100, s102, s161, s185, s195, s198],
  [s22, s102, s133, s185, s189, s195, s198],
  [s22, s102, s133, s185, s195, s196, s198],
  [s22, s102, s161, s180, s185, s195, s198],
  [s43, s102, s108, s161, s185, s195, s198]]
def b7_27 : List (List Sig) := [
  [s13, s43, s102, s161, s185, s195, s198],
  [s22, s43, s102, s137, s185, s195, s198],
  [s23, s43, s102, s133, s185, s195, s198],
  [s43, s54, s102, s161, s185, s195, s198],
  [s43, s104, s161, s185, s195, s198]]
def b7_28 : List (List Sig) := [
  [s5, s22, s27, s102, s161, s185, s195, s198],
  [s5, s22, s43, s88, s161, s185, s195, s198],
  [s8, s27, s102, s161, s185, s195, s198],
  [s8, s43, s88, s161, s185, s195, s198],
  [s9, s43, s102, s153, s185, s195, s198],
  [s22, s27, s43, s72, s102, s185, s195, s198],
  [s22, s43, s102, s130, s185, s195, s198],
  [s42, s43, s102, s161, s185, s195, s198]]
def b7_29 : List (List Sig) := [
  [s2, s43, s102, s161, s185, s195, s198],
  [s5, s22, s48, s102, s161, s185, s195, s198],
  [s5, s22, s88, s161, s185, s195, s198],
  [s5, s38, s102, s161, s185, s195, s198],
  [s22, s27, s72, s102, s185, s195, s198],
  [s22, s43, s48, s72, s102, s185, s195, s198],
  [s22, s43, s48, s96, s102, s161, s185, s195],
  [s22, s43, s102, s169, s185, s195, s198],
  [s43, s55, s102, s153, s185, s195, s198],
  [s43, s102, s126, s161, s185, s188, s195]]
def b7_30 : List (List Sig) := [
  [s5, s43, s102, s133, s161, s195, s198, s205],
  [s22, s29, s102, s161, s185, s195, s198],
  [s22, s43, s47, s102, s133, s195, s198],
  [s24, s43, s102, s161, s172, s185, s198]]
def bucketTier7 : List (List (List Sig)) := [b7_0, b7_1, b7_2, b7_3, b7_4, b7_5, b7_6, b7_7, b7_8, b7_9, b7_10, b7_11, b7_12, b7_13, b7_14, b7_15, b7_16, b7_17, b7_18, b7_19, b7_20, b7_21, b7_22, b7_23, b7_24, b7_25, b7_26, b7_27, b7_28, b7_29, b7_30]

def b8_1 : List (List Sig) := [
  [s6, s22, s43, s102, s161, s185, s195, s198],
  [s22, s43, s45, s102, s161, s185, s195, s198]]
def b8_3 : List (List Sig) := [
  [s0, s5, s43, s102, s161, s185, s195, s198],
  [s5, s43, s102, s106, s161, s185, s195, s198],
  [s5, s43, s102, s133, s161, s185, s195, s198],
  [s5, s43, s102, s161, s162, s185, s195, s198],
  [s5, s43, s102, s161, s166, s185, s195, s198],
  [s5, s43, s102, s161, s185, s195, s198, s204],
  [s22, s43, s85, s102, s185, s195, s198],
  [s43, s49, s102, s161, s185, s195],
  [s43, s50, s102, s161, s185, s195]]
def b8_4 : List (List Sig) := [
  [s7, s43, s72, s102, s161, s185, s195, s198],
  [s40, s43, s102, s161, s185, s195, s198],
  [s43, s102, s106, s133, s161, s185, s195, s198],
  [s43, s102, s114, s122, s161, s185, s195, s198],
  [s43, s102, s128, s161, s185, s195, s198]]
def b8_5 : List (List Sig) := [
  [s19, s22, s43, s102, s161, s185, s195, s198],
  [s19, s43, s102, s161, s185, s195, s198],
  [s22, s34, s43, s102, s161, s185, s195, s198],
  [s22, s43, s72, s102, s161, s185, s195, s198],
  [s22, s43, s102, s114, s161, s185, s195, s198],
  [s22, s43, s102, s117, s161, s185, s195, s198],
  [s22, s43, s102, s119, s161, s185, s195, s198],
  [s34, s43, s102, s161, s185, s195, s198],
  [s43, s102, s111, s161, s185, s195, s198],
  [s43, s102, s113, s161, s185, s195, s198],
  [s43, s102, s114, s161, s185, s195, s198],
  [s43, s102, s121, s161, s185, s195, s198],
  [s43, s102, s134, s161, s185, s195, s198]]
def b8_6 : List (List Sig) := [
  [s34, s43, s114, s161, s185, s195, s198],
  [s43, s114, s117, s161, s185, s195, s198],
  [s43, s114, s119, s161, s185, s195, s198]]
def b8_7 : List (List Sig) := [
  [s14, s43, s102, s161, s185, s195, s198]]
def b8_8 : List (List Sig) := [
  [s5, s43, s102, s161, s185, s195, s198, s203],
  [s22, s43, s84, s102, s185, s195, s198],
  [s22, s43, s88, s102, s161, s185, s195, s198],
  [s43, s45, s102, s161, s185, s188, s195],
  [s43, s102, s133, s153, s185, s195, s198]]
def b8_10 : List (List Sig) := [
  [s5, s43, s45, s102, s161, s185, s195, s198],
  [s43, s47, s102, s133, s161, s195, s198],
  [s43, s102, s161, s185, s195, s199]]
def b8_11 : List (List Sig) := [
  [s43, s102, s114, s161, s172, s185, s195, s198]]
def b8_12 : List (List Sig) := [
  [s43, s102, s133, s161, s185, s188, s195, s198]]
def b8_13 : List (List Sig) := [
  [s43, s50, s102, s106, s161, s185, s195]]
def b8_14 : List (List Sig) := [
  [s5, s34, s43, s102, s161, s185, s195, s198],
  [s5, s43, s102, s114, s161, s185, s195, s198],
  [s5, s43, s106, s161, s185, s195, s198],
  [s7, s22, s43, s102, s161, s185, s195, s198],
  [s7, s43, s102, s161, s185, s195, s196],
  [s8, s43, s102, s120, s161, s185, s195, s198],
  [s9, s22, s43, s102, s161, s185, s195, s198],
  [s9, s43, s102, s161, s185, s195, s198],
  [s22, s43, s47, s102, s161, s185, s195, s198],
  [s22, s43, s102, s133, s185, s195, s198],
  [s22, s43, s102, s166, s185, s195, s198],
  [s25, s43, s102, s161, s185, s195, s198],
  [s39, s43, s102, s161, s185, s195, s198],
  [s43, s57, s102, s161, s185, s195, s198],
  [s43, s102, s122, s161, s185, s195, s198]]
def b8_15 : List (List Sig) := [
  [s5, s34, s102, s161, s185, s195, s198],
  [s5, s106, s161, s185, s195, s198],
  [s22, s43, s102, s154, s185, s195, s198],
  [s22, s43, s102, s161, s185, s195, s198],
  [s24, s43, s102, s161, s185, s195, s198],
  [s25, s102, s161, s185, s195, s198],
  [s34, s43, s102, s133, s161, s185, s195, s198],
  [s36, s43, s102, s161, s185, s195, s198],
  [s39, s102, s161, s185, s195, s198],
  [s43, s55, s102, s161, s185, s195, s198],
  [s43, s80, s102, s185, s195, s198],
  [s43, s102, s107, s161, s185, s195, s198],
  [s43, s102, s111, s133, s161, s185, s195, s198],
  [s43, s102, s114, s133, s161, s185, s195, s198],
  [s43, s102, s116, s161, s185, s195, s198],
  [s43, s102, s143, s185, s195, s198],
  [s43, s102, s148, s185, s198, s204],
  [s43, s102, s151, s185, s195, s198],
  [s43, s102, s159, s185, s195, s198]]
def b8_16 : List (List Sig) := [
  [s5, s43, s102, s148, s161, s185, s195, s198],
  [s22, s43, s94, s102, s161, s185, s195, s198],
  [s34, s43, s97, s102, s161, s185, s195, s198],
  [s34, s43, s102, s154, s161, s185, s195, s198],
  [s43, s102, s114, s154, s161, s185, s195, s198],
  [s43, s102, s114, s161, s178, s185, s195, s198],
  [s43, s102, s114, s161, s185, s189, s195, s198],
  [s43, s102, s158, s161, s185, s195, s198],
  [s43, s121, s161, s185, s195, s198]]
def b8_17 : List (List Sig) := [
  [s43, s102, s123, s161, s185, s195, s198]]
def b8_18 : List (List Sig) := [
  [s22, s27, s43, s102, s161, s185, s195, s198],
  [s43, s56, s102, s161, s185, s195, s198]]
def b8_19 : List (List Sig) := [
  [s22, s27, s102, s161, s185, s195, s198],
  [s22, s43, s48, s102, s161, s185, s195, s198],
  [s38, s43, s102, s161, s185, s195, s198]]
def b8_20 : List (List Sig) := [
  [s38, s102, s161, s185, s195, s198]]
def b8_21 : List (List Sig) := [
  [s22, s43, s102, s161, s172, s185, s195, s198],
  [s43, s102, s133, s161, s195, s198, s205]]
def b8_22 : List (List Sig) := [
  [s43, s102, s126, s161, s185, s195, s198],
  [s43, s102, s148, s161, s176, s185, s195, s198]]
def b8_23 : List (List Sig) := [
  [s4, s5, s43, s102, s161, s185, s195, s198],
  [s5, s7, s43, s102, s161, s185, s195, s198],
  [s5, s43, s47, s102, s161, s185, s195, s198]]
def b8_24 : List (List Sig) := [
  [s5, s22, s43, s102, s161, s185, s195, s198],
  [s5, s43, s102, s161, s185, s195, s198],
  [s7, s43, s96, s102, s161, s185, s195],
  [s8, s43, s102, s161, s185, s195, s198],
  [s9, s43, s102, s133, s161, s185, s195, s198]]
def b8_25 : List (List Sig) := [
  [s0, s22, s43, s102, s161, s185, s195, s198],
  [s0, s43, s102, s161, s185, s195, s198],
  [s5, s22, s102, s161, s185, s195, s198],
  [s5, s43, s102, s158, s161, s185, s195, s198],
  [s5, s43, s114, s161, s185, s195, s198],
  [s22, s43, s72, s102, s185, s195, s198],
  [s22, s43, s102, s133, s161, s185, s195, s198],
  [s22, s43, s102, s161, s185, s195, s198, s201],
  [s22, s43, s102, s161, s185, s195, s198, s205],
  [s43, s64, s102, s161, s185, s195, s198],
  [s43, s80, s102, s106, s185, s195, s198],
  [s43, s83, s102, s161, s185, s195, s198],
  [s43, s102, s106, s161, s185, s195, s198],
  [s43, s102, s133, s161, s185, s195, s198],
  [s43, s102, s134, s185, s195, s198],
  [s43, s102, s135, s161, s185, s195, s198],
  [s43, s102, s141, s161, s185, s195, s198],
  [s43, s102, s146, s161, s185, s195, s198]]
def b8_26 : List (List Sig) := [
  [s34, s43, s106, s161, s185, s195, s198],
  [s43, s80, s102, s161, s185, s195, s198],
  [s43, s102, s143, s161, s185, s195, s198]]
def b8_27 : List (List Sig) := [
  [s17, s43, s102, s161, s185, s195, s198],
  [s22, s32, s102, s161, s185, s195, s198],
  [s22, s43, s102, s148, s185, s195, s198],
  [s22, s97, s102, s161, s185, s195, s198],
  [s22, s102, s161, s178, s185, s195, s198],
  [s22, s102, s161, s185, s189, s195, s198],
  [s34, s43, s97, s161, s185, s195, s198]]
def b8_28 : List (List Sig) := [
  [s7, s43, s102, s153, s161, s185, s195],
  [s23, s43, s102, s161, s185, s195, s198]]
def b8_30 : List (List Sig) := [
  [s22, s43, s102, s161, s176, s185, s195, s198]]
def bucketTier8 : List (List (List Sig)) := [[], b8_1, [], b8_3, b8_4, b8_5, b8_6, b8_7, b8_8, [], b8_10, b8_11, b8_12, b8_13, b8_14, b8_15, b8_16, b8_17, b8_18, b8_19, b8_20, b8_21, b8_22, b8_23, b8_24, b8_25, b8_26, b8_27, b8_28, [], b8_30]

def b9_1 : List (List Sig) := [
  [s43, s45, s102, s161, s185, s195, s198]]
def b9_5 : List (List Sig) := [
  [s34, s43, s102, s161, s185, s195, s198],
  [s43, s102, s114, s161, s185, s195, s198]]
def b9_7 : List (List Sig) := [
  [s43, s102, s148, s161, s185, s195, s198]]
def b9_14 : List (List Sig) := [
  [s7, s43, s102, s161, s185, s195, s198],
  [s43, s47, s102, s161, s185, s195, s198]]
def b9_15 : List (List Sig) := [
  [s22, s43, s102, s161, s185, s195, s198]]
def b9_24 : List (List Sig) := [
  [s5, s43, s102, s161, s185, s195, s198]]
def b9_25 : List (List Sig) := [
  [s43, s102, s106, s161, s185, s195, s198],
  [s43, s102, s133, s161, s185, s195, s198],
  [s43, s102, s161, s166, s185, s195, s198],
  [s43, s102, s161, s185, s195, s198, s204]]
def b9_30 : List (List Sig) := [
  [s43, s102, s161, s185, s195, s198, s203]]
def bucketTier9 : List (List (List Sig)) := [[], b9_1, [], [], [], b9_5, [], b9_7, [], [], [], [], [], [], b9_14, b9_15, [], [], [], [], [], [], [], [], b9_24, b9_25, [], [], [], [], b9_30]

def b10_15 : List (List Sig) := [
  [s43, s102, s161, s185, s195, s198]]
def bucketTier10 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], b10_15, [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def buckets : ℕ → List (List (List Sig))
  | 1 => bucketTier1
  | 2 => bucketTier2
  | 3 => bucketTier3
  | 4 => bucketTier4
  | 5 => bucketTier5
  | 6 => bucketTier6
  | 7 => bucketTier7
  | 8 => bucketTier8
  | 9 => bucketTier9
  | 10 => bucketTier10
  | _ => []

def tiers (n : ℕ) : List (List Sig) := (buckets n).flatten
def lookup (n : ℕ) (w : List Sig) : Bool := bucketHas w (buckets n) (hashBucket w)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma lookup_sound (n : ℕ) (w : List Sig) (h : lookup n w = true) : w ∈ tiers n :=
  bucketHas_sound w _ _ h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma startND : (minorRaw (0 : Fin 7)).Nodup := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma sortedStart : sortSignals (minorRaw (0 : Fin 7)) ∈ tiers 10 := by decide +kernel
end Minor0

namespace Minor1
def group : List PermRows := [
  (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (#[0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 7, 8, 9, 10, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8]),
  (#[0, 3, 5, 1, 4, 2, 6, 7, 10, 9, 8, 11, 14, 13, 12, 15], #[0, 1, 6, 3, 4, 7, 2, 5, 8, 9]),
  (#[0, 3, 5, 1, 4, 2, 6, 11, 14, 13, 12, 7, 10, 9, 8, 15], #[0, 1, 6, 3, 4, 7, 2, 5, 9, 8]),
  (#[0, 1, 2, 4, 3, 6, 5, 8, 7, 9, 10, 12, 11, 13, 14, 15], #[0, 2, 1, 3, 5, 4, 6, 7, 8, 9]),
  (#[0, 1, 2, 4, 3, 6, 5, 12, 11, 13, 14, 8, 7, 9, 10, 15], #[0, 2, 1, 3, 5, 4, 6, 7, 9, 8]),
  (#[0, 4, 6, 1, 3, 2, 5, 8, 10, 9, 7, 12, 14, 13, 11, 15], #[0, 2, 6, 3, 5, 7, 1, 4, 8, 9]),
  (#[0, 4, 6, 1, 3, 2, 5, 12, 14, 13, 11, 8, 10, 9, 7, 15], #[0, 2, 6, 3, 5, 7, 1, 4, 9, 8]),
  (#[0, 3, 5, 4, 1, 6, 2, 10, 7, 9, 8, 14, 11, 13, 12, 15], #[0, 6, 1, 3, 7, 4, 2, 5, 8, 9]),
  (#[0, 3, 5, 4, 1, 6, 2, 14, 11, 13, 12, 10, 7, 9, 8, 15], #[0, 6, 1, 3, 7, 4, 2, 5, 9, 8]),
  (#[0, 4, 6, 3, 1, 5, 2, 10, 8, 9, 7, 14, 12, 13, 11, 15], #[0, 6, 2, 3, 7, 5, 1, 4, 8, 9]),
  (#[0, 4, 6, 3, 1, 5, 2, 14, 12, 13, 11, 10, 8, 9, 7, 15], #[0, 6, 2, 3, 7, 5, 1, 4, 9, 8])]
def s0 : Sig := (0x6, 0xfffffffffffffc3f)
def s1 : Sig := (0x1a, 0xfffffffffffffc47)
def s2 : Sig := (0x28, 0xfffffffffffffcdb)
def s3 : Sig := (0x2e, 0x12)
def s4 : Sig := (0x2e, 0xfffffffffffffcff)
def s5 : Sig := (0x7e, 0xfffffffffffffcff)
def s6 : Sig := (0x86, 0x12)
def s7 : Sig := (0xae, 0x12)
def s8 : Sig := (0xfe, 0xfffffffffffffcff)
def s9 : Sig := (0x182, 0xfffffffffffffd07)
def s10 : Sig := (0x186, 0xfffffffffffffd37)
def s11 : Sig := (0x186, 0xfffffffffffffd3f)
def s12 : Sig := (0x1fe, 0x36)
def s13 : Sig := (0x1fe, 0xfffffffffffffcff)
def s14 : Sig := (0x27e, 0xfffffffffffffcff)
def s15 : Sig := (0x280, 0xfffffffffffffd1b)
def s16 : Sig := (0x286, 0xfffffffffffffd3f)
def s17 : Sig := (0x2d0, 0xfffffffffffffd1b)
def s18 : Sig := (0x380, 0x100)
def s19 : Sig := (0x380, 0xfffffffffffffd3f)
def s20 : Sig := (0x386, 0xfffffffffffffd3f)
def s21 : Sig := (0x3ae, 0xfffffffffffffd3f)
def s22 : Sig := (0x3e6, 0xfffffffffffffdbf)
def s23 : Sig := (0x3fe, 0xfffffffffffffdff)
def s24 : Sig := (0x59a, 0xfffffffffffffd47)
def s25 : Sig := (0x6a8, 0xfffffffffffffddb)
def s26 : Sig := (0x6ae, 0xfffffffffffffddb)
def s27 : Sig := (0x6ec, 0xfffffffffffffdfb)
def s28 : Sig := (0x6f8, 0xfffffffffffffddb)
def s29 : Sig := (0x6fe, 0xfffffffffffffdff)
def s30 : Sig := (0x700, 0xfffffffffffffded)
def s31 : Sig := (0x750, 0xfffffffffffffded)
def s32 : Sig := (0x780, 0x100)
def s33 : Sig := (0x786, 0xfffffffffffffd3f)
def s34 : Sig := (0x7a8, 0xfffffffffffffddb)
def s35 : Sig := (0x7ae, 0x112)
def s36 : Sig := (0x7ae, 0xfffffffffffffdff)
def s37 : Sig := (0x7f8, 0xfffffffffffffdff)
def s38 : Sig := (0x7fe, 0x136)
def s39 : Sig := (0x7fe, 0xfffffffffffffdff)
def s40 : Sig := (0x882, 0x2)
def s41 : Sig := (0x886, 0x12)
def s42 : Sig := (0x88a, 0x2)
def s43 : Sig := (0x8a8, 0x12)
def s44 : Sig := (0xb86, 0xfffffffffffffd3f)
def s45 : Sig := (0xea8, 0xfffffffffffffddb)
def s46 : Sig := (0x1106, 0x24)
def s47 : Sig := (0x1112, 0x4)
def s48 : Sig := (0x1150, 0x24)
def s49 : Sig := (0x1806, 0xfffffffffffffe3f)
def s50 : Sig := (0x1982, 0xffffffffffffff07)
def s51 : Sig := (0x1986, 0x36)
def s52 : Sig := (0x199a, 0x6)
def s53 : Sig := (0x19f8, 0x36)
def s54 : Sig := (0x2200, 0x18)
def s55 : Sig := (0x2204, 0x38)
def s56 : Sig := (0x2206, 0xfffffffffffffc3f)
def s57 : Sig := (0x2220, 0x98)
def s58 : Sig := (0x2228, 0xfffffffffffffcdb)
def s59 : Sig := (0x2240, 0xa8)
def s60 : Sig := (0x227e, 0xfffffffffffffcff)
def s61 : Sig := (0x2386, 0xfffffffffffffd3f)
def s62 : Sig := (0x26a8, 0xfffffffffffffddb)
def s63 : Sig := (0x2800, 0xfffffffffffffe1b)
def s64 : Sig := (0x2a80, 0xffffffffffffff1b)
def s65 : Sig := (0x2a86, 0x3a)
def s66 : Sig := (0x2aa8, 0x9a)
def s67 : Sig := (0x2b86, 0xfffffffffffffd3f)
def s68 : Sig := (0x3300, 0xffffffffffffff2d)
def s69 : Sig := (0x3306, 0x3c)
def s70 : Sig := (0x3350, 0xac)
def s71 : Sig := (0x3800, 0xfffffffffffffe3f)
def s72 : Sig := (0x3806, 0xfffffffffffffe3f)
def s73 : Sig := (0x382e, 0xfffffffffffffe3f)
def s74 : Sig := (0x3856, 0xfffffffffffffe3f)
def s75 : Sig := (0x3886, 0xfffffffffffffe3f)
def s76 : Sig := (0x3a06, 0xfffffffffffffe3f)
def s77 : Sig := (0x3b86, 0x3e)
def s78 : Sig := (0x3b86, 0xffffffffffffff3f)
def s79 : Sig := (0x3bf8, 0xbe)
def s80 : Sig := (0x4418, 0x40)
def s81 : Sig := (0x4428, 0xc0)
def s82 : Sig := (0x4ca8, 0xd2)
def s83 : Sig := (0x552e, 0xe4)
def s84 : Sig := (0x5550, 0xe4)
def s85 : Sig := (0x581a, 0xfffffffffffffe47)
def s86 : Sig := (0x5d80, 0x300)
def s87 : Sig := (0x5d9a, 0xffffffffffffff47)
def s88 : Sig := (0x5dae, 0x312)
def s89 : Sig := (0x6628, 0xd8)
def s90 : Sig := (0x6828, 0xfffffffffffffedb)
def s91 : Sig := (0x682e, 0xfffffffffffffedb)
def s92 : Sig := (0x6878, 0xfffffffffffffedb)
def s93 : Sig := (0x68a8, 0xfffffffffffffedb)
def s94 : Sig := (0x6a28, 0xfffffffffffffedb)
def s95 : Sig := (0x6c28, 0xfffffffffffffedb)
def s96 : Sig := (0x6ea8, 0xda)
def s97 : Sig := (0x6ea8, 0xffffffffffffffdb)
def s98 : Sig := (0x7050, 0xfffffffffffffeed)
def s99 : Sig := (0x772e, 0xfc)
def s100 : Sig := (0x7750, 0xec)
def s101 : Sig := (0x7750, 0xffffffffffffffed)
def s102 : Sig := (0x7800, 0x200)
def s103 : Sig := (0x7828, 0xfffffffffffffedb)
def s104 : Sig := (0x782e, 0x212)
def s105 : Sig := (0x782e, 0xfffffffffffffeff)
def s106 : Sig := (0x7878, 0xfffffffffffffedb)
def s107 : Sig := (0x7878, 0xfffffffffffffeff)
def s108 : Sig := (0x787e, 0x2d2)
def s109 : Sig := (0x787e, 0xfffffffffffffeff)
def s110 : Sig := (0x7f80, 0x300)
def s111 : Sig := (0x7fae, 0x312)
def s112 : Sig := (0x7ffe, 0xffffffffffffffff)
def s113 : Sig := (0x8000, 0xffffffffffffff01)
def s114 : Sig := (0x8006, 0xfffffffffffffc3f)
def s115 : Sig := (0x8180, 0x100)
def s116 : Sig := (0x8280, 0x100)
def s117 : Sig := (0x8380, 0x100)
def s118 : Sig := (0x8386, 0xfffffffffffffd3f)
def s119 : Sig := (0x8580, 0x100)
def s120 : Sig := (0x8680, 0x100)
def s121 : Sig := (0x86a8, 0xfffffffffffffddb)
def s122 : Sig := (0x8700, 0x100)
def s123 : Sig := (0x8880, 0xffffffffffffff03)
def s124 : Sig := (0x8880, 0xffffffffffffff13)
def s125 : Sig := (0x8880, 0xffffffffffffff1b)
def s126 : Sig := (0x8882, 0xffffffffffffff03)
def s127 : Sig := (0x8886, 0xffffffffffffff13)
def s128 : Sig := (0x888a, 0xffffffffffffff03)
def s129 : Sig := (0x88a8, 0xffffffffffffff13)
def s130 : Sig := (0x8980, 0xffffffffffffff03)
def s131 : Sig := (0x8982, 0xffffffffffffff07)
def s132 : Sig := (0x8b86, 0x112)
def s133 : Sig := (0x8d80, 0xffffffffffffff03)
def s134 : Sig := (0x8d8a, 0x102)
def s135 : Sig := (0x9100, 0xffffffffffffff05)
def s136 : Sig := (0x9100, 0xffffffffffffff25)
def s137 : Sig := (0x9980, 0x300)
def s138 : Sig := (0x9980, 0xffffffffffffff07)
def s139 : Sig := (0x9982, 0xffffffffffffff07)
def s140 : Sig := (0x9986, 0x312)
def s141 : Sig := (0x9986, 0xffffffffffffff17)
def s142 : Sig := (0x9986, 0xffffffffffffff27)
def s143 : Sig := (0x9986, 0xffffffffffffff37)
def s144 : Sig := (0x9986, 0xffffffffffffff3f)
def s145 : Sig := (0x998a, 0xffffffffffffff07)
def s146 : Sig := (0x9992, 0xffffffffffffff07)
def s147 : Sig := (0x9d80, 0x300)
def s148 : Sig := (0x9d82, 0xffffffffffffff07)
def s149 : Sig := (0x9d9a, 0xffffffffffffff47)
def s150 : Sig := (0x9ff8, 0x136)
def s151 : Sig := (0xa200, 0xffffffffffffff09)
def s152 : Sig := (0xa206, 0xfffffffffffffc3f)
def s153 : Sig := (0xaa80, 0xffffffffffffff1b)
def s154 : Sig := (0xaa84, 0xffffffffffffff3b)
def s155 : Sig := (0xaa86, 0xffffffffffffff1b)
def s156 : Sig := (0xaaa0, 0xffffffffffffff9b)
def s157 : Sig := (0xaaa8, 0xffffffffffffff1b)
def s158 : Sig := (0xab80, 0xffffffffffffff1b)
def s159 : Sig := (0xab86, 0xffffffffffffff3f)
def s160 : Sig := (0xae80, 0xffffffffffffff1b)
def s161 : Sig := (0xb300, 0xffffffffffffff2d)
def s162 : Sig := (0xb806, 0xfffffffffffffe3f)
def s163 : Sig := (0xba80, 0xffffffffffffff1b)
def s164 : Sig := (0xba86, 0xffffffffffffff3f)
def s165 : Sig := (0xbb80, 0x300)
def s166 : Sig := (0xbb80, 0xffffffffffffff1b)
def s167 : Sig := (0xbb80, 0xffffffffffffff3f)
def s168 : Sig := (0xbb86, 0x312)
def s169 : Sig := (0xbb86, 0xffffffffffffff3f)
def s170 : Sig := (0xbffe, 0xffffffffffffffff)
def s171 : Sig := (0xc400, 0xffffffffffffff41)
def s172 : Sig := (0xc400, 0xffffffffffffffc1)
def s173 : Sig := (0xc6a8, 0x1c0)
def s174 : Sig := (0xc800, 0x200)
def s175 : Sig := (0xcc88, 0xffffffffffffff43)
def s176 : Sig := (0xcc8a, 0xffffffffffffff43)
def s177 : Sig := (0xcc98, 0xffffffffffffff43)
def s178 : Sig := (0xcca8, 0xffffffffffffff53)
def s179 : Sig := (0xcca8, 0xffffffffffffffc3)
def s180 : Sig := (0xcca8, 0xffffffffffffffdb)
def s181 : Sig := (0xcd88, 0xffffffffffffff43)
def s182 : Sig := (0xd510, 0xffffffffffffff45)
def s183 : Sig := (0xd550, 0xffffffffffffffe5)
def s184 : Sig := (0xd550, 0xffffffffffffffed)
def s185 : Sig := (0xd800, 0x200)
def s186 : Sig := (0xd88a, 0x202)
def s187 : Sig := (0xdc88, 0xffffffffffffff43)
def s188 : Sig := (0xdc98, 0xffffffffffffff43)
def s189 : Sig := (0xdc9a, 0xffffffffffffff47)
def s190 : Sig := (0xdd80, 0x300)
def s191 : Sig := (0xdd8a, 0x302)
def s192 : Sig := (0xdd98, 0x340)
def s193 : Sig := (0xdd9a, 0xffffffffffffff47)
def s194 : Sig := (0xddfe, 0xffffffffffffffff)
def s195 : Sig := (0xe600, 0xffffffffffffffc9)
def s196 : Sig := (0xe6a8, 0xffffffffffffffdb)
def s197 : Sig := (0xe800, 0x200)
def s198 : Sig := (0xe828, 0xfffffffffffffedb)
def s199 : Sig := (0xe8a8, 0x212)
def s200 : Sig := (0xec28, 0xfffffffffffffedb)
def s201 : Sig := (0xee28, 0xffffffffffffffdb)
def s202 : Sig := (0xee80, 0x300)
def s203 : Sig := (0xeea8, 0x3c0)
def s204 : Sig := (0xeea8, 0xffffffffffffffdb)
def s205 : Sig := (0xeffe, 0xffffffffffffffff)
def s206 : Sig := (0xf000, 0x200)
def s207 : Sig := (0xf150, 0x224)
def s208 : Sig := (0xf700, 0xffffffffffffffed)
def s209 : Sig := (0xf750, 0xffffffffffffffed)
def s210 : Sig := (0xfefe, 0xffffffffffffffff)
def s211 : Sig := (0xffae, 0xffffffffffffffff)
def s212 : Sig := (0xfff8, 0xffffffffffffffff)
def bucketTier1 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def bucketTier2 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def bucketTier3 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def b4_3 : List (List Sig) := [
  [s0, s2, s64, s193, s209],
  [s0, s2, s87, s153, s209],
  [s0, s2, s101, s153, s193],
  [s4, s15, s63, s193, s209],
  [s5, s15, s63, s193, s208]]
def b4_5 : List (List Sig) := [
  [s10, s25, s109, s136, s195]]
def b4_7 : List (List Sig) := [
  [s5, s64, s68, s193, s195],
  [s5, s64, s161, s193, s195],
  [s5, s87, s153, s161, s195]]
def b4_12 : List (List Sig) := [
  [s5, s11, s90, s125, s209],
  [s5, s20, s90, s125, s209],
  [s5, s20, s90, s153, s184]]
def b4_17 : List (List Sig) := [
  [s5, s20, s90, s124, s209],
  [s5, s20, s90, s127, s209],
  [s5, s20, s90, s153, s183]]
def b4_19 : List (List Sig) := [
  [s4, s30, s98, s153, s193],
  [s4, s31, s98, s153, s193]]
def b4_27 : List (List Sig) := [
  [s5, s19, s71, s193, s195],
  [s5, s19, s72, s193, s195]]
def bucketTier4 : List (List (List Sig)) := [[], [], [], b4_3, [], b4_5, [], b4_7, [], [], [], [], b4_12, [], [], [], [], b4_17, [], b4_19, [], [], [], [], [], [], [], b4_27, [], [], []]

def b5_0 : List (List Sig) := [
  [s20, s25, s59, s72, s90, s209]]
def b5_1 : List (List Sig) := [
  [s0, s15, s39, s90, s139, s209],
  [s5, s15, s20, s90, s139, s209]]
def b5_3 : List (List Sig) := [
  [s111, s169, s190, s204, s209]]
def b5_4 : List (List Sig) := [
  [s19, s37, s109, s139, s195],
  [s19, s39, s109, s138, s195],
  [s19, s39, s109, s139, s195],
  [s20, s37, s109, s139, s195],
  [s20, s39, s107, s139, s195]]
def b5_5 : List (List Sig) := [
  [s5, s11, s49, s204, s209],
  [s5, s20, s72, s180, s209],
  [s5, s56, s78, s204, s209],
  [s5, s56, s97, s169, s209],
  [s5, s61, s76, s204, s209],
  [s5, s78, s190, s195, s204, s209],
  [s5, s152, s169, s204, s209]]
def b5_6 : List (List Sig) := [
  [s4, s36, s109, s123, s153, s209],
  [s4, s39, s109, s123, s153, s209],
  [s5, s19, s71, s193, s204, s209],
  [s5, s19, s72, s193, s204, s209],
  [s5, s19, s109, s167, s193, s195],
  [s5, s19, s109, s169, s193, s195],
  [s5, s20, s58, s72, s204, s209],
  [s5, s20, s72, s179, s204, s209],
  [s5, s20, s72, s193, s195, s212],
  [s5, s20, s107, s169, s193, s195],
  [s5, s20, s109, s167, s193, s195],
  [s5, s36, s109, s123, s153, s209],
  [s5, s39, s109, s123, s153, s208],
  [s15, s39, s105, s109, s123, s209],
  [s19, s37, s72, s109, s193, s195],
  [s19, s39, s71, s109, s193, s195],
  [s19, s39, s72, s109, s193, s195],
  [s20, s37, s72, s109, s193, s195]]
def b5_7 : List (List Sig) := [
  [s5, s64, s78, s182, s204, s209],
  [s5, s64, s169, s182, s204, s209],
  [s5, s78, s153, s182, s204, s209],
  [s15, s39, s99, s109, s209]]
def b5_8 : List (List Sig) := [
  [s5, s20, s55, s90, s153, s209],
  [s20, s25, s55, s72, s90, s209]]
def b5_9 : List (List Sig) := [
  [s5, s15, s72, s123, s204, s209],
  [s5, s20, s90, s123, s153, s209],
  [s15, s39, s72, s90, s123, s209],
  [s20, s109, s121, s139, s195, s209]]
def b5_12 : List (List Sig) := [
  [s5, s88, s169, s204, s209],
  [s20, s25, s109, s124, s209],
  [s20, s25, s109, s127, s209],
  [s20, s25, s109, s153, s183]]
def b5_13 : List (List Sig) := [
  [s0, s2, s78, s193, s204, s209],
  [s0, s2, s87, s169, s204, s209],
  [s0, s2, s101, s169, s193, s204],
  [s0, s2, s112, s153, s193, s209],
  [s0, s5, s64, s97, s193, s209],
  [s0, s5, s64, s193, s204, s209],
  [s0, s5, s87, s153, s204, s209],
  [s0, s5, s97, s153, s193, s209],
  [s4, s15, s105, s153, s193, s209],
  [s4, s15, s109, s153, s193, s209],
  [s5, s15, s63, s193, s209, s211],
  [s5, s15, s105, s153, s193, s209],
  [s5, s15, s109, s153, s193, s208],
  [s5, s20, s90, s153, s193, s209],
  [s5, s20, s90, s155, s193, s209],
  [s5, s20, s90, s160, s193, s209],
  [s5, s20, s91, s153, s193, s209],
  [s5, s20, s93, s153, s193, s209],
  [s5, s20, s94, s153, s193, s209],
  [s5, s20, s95, s153, s193, s209],
  [s5, s20, s103, s153, s193, s209],
  [s5, s64, s78, s190, s204, s209],
  [s5, s64, s169, s190, s204, s209],
  [s5, s78, s153, s190, s204, s209],
  [s5, s86, s153, s169, s204, s209],
  [s8, s20, s90, s153, s193, s209],
  [s15, s36, s63, s109, s193, s209],
  [s15, s39, s63, s109, s193, s208],
  [s20, s25, s72, s90, s193, s209],
  [s20, s25, s72, s91, s193, s209],
  [s20, s25, s72, s92, s193, s209],
  [s20, s25, s72, s93, s193, s209],
  [s20, s25, s72, s193, s198, s209]]
def b5_14 : List (List Sig) := [
  [s5, s20, s72, s178, s204, s209],
  [s20, s25, s98, s109, s139, s195]]
def b5_15 : List (List Sig) := [
  [s5, s20, s73, s182, s204, s209],
  [s10, s25, s109, s143, s195, s209],
  [s10, s39, s109, s124, s195, s209],
  [s20, s39, s109, s153, s172, s183]]
def b5_16 : List (List Sig) := [
  [s5, s20, s90, s141, s204, s209]]
def b5_17 : List (List Sig) := [
  [s5, s64, s68, s193, s204, s209],
  [s5, s64, s78, s193, s195, s209],
  [s5, s64, s161, s193, s204, s209],
  [s5, s78, s153, s193, s195, s209],
  [s5, s87, s153, s161, s204, s209],
  [s5, s112, s153, s161, s193, s195],
  [s20, s25, s100, s109, s209],
  [s20, s109, s121, s153, s182, s209],
  [s39, s64, s68, s109, s193, s195],
  [s39, s64, s109, s161, s193, s195],
  [s39, s87, s109, s153, s161, s195]]
def b5_19 : List (List Sig) := [
  [s4, s36, s109, s153, s182, s209],
  [s4, s39, s109, s153, s182, s209],
  [s5, s36, s109, s153, s182, s209],
  [s5, s39, s109, s138, s167, s195],
  [s5, s39, s109, s139, s167, s195],
  [s20, s39, s107, s109, s139, s195]]
def b5_22 : List (List Sig) := [
  [s5, s11, s90, s144, s204, s209],
  [s5, s11, s109, s125, s204, s209],
  [s5, s20, s57, s98, s161, s204],
  [s5, s20, s72, s180, s204, s209],
  [s5, s20, s90, s139, s153, s209],
  [s5, s20, s90, s144, s204, s209],
  [s5, s20, s90, s153, s182, s209],
  [s5, s20, s90, s153, s194, s209],
  [s5, s20, s90, s169, s184, s204],
  [s5, s20, s109, s125, s180, s209],
  [s5, s20, s109, s125, s204, s209],
  [s5, s20, s109, s153, s184, s204],
  [s5, s56, s97, s169, s204, s209],
  [s15, s36, s109, s123, s209],
  [s15, s39, s105, s123, s209],
  [s15, s39, s109, s123, s208],
  [s20, s25, s72, s90, s139, s209],
  [s20, s25, s72, s90, s182, s209],
  [s20, s25, s98, s109, s153, s182]]
def b5_24 : List (List Sig) := [
  [s5, s20, s73, s175, s204, s209]]
def b5_25 : List (List Sig) := [
  [s0, s5, s97, s161, s193, s209],
  [s5, s20, s66, s72, s204, s209],
  [s5, s20, s66, s98, s169, s204],
  [s8, s31, s72, s161, s193, s204]]
def b5_26 : List (List Sig) := [
  [s39, s109, s124, s136, s195]]
def b5_27 : List (List Sig) := [
  [s0, s78, s190, s204, s209],
  [s0, s86, s169, s204, s209],
  [s0, s97, s169, s190, s209],
  [s5, s20, s109, s124, s204, s209],
  [s5, s20, s109, s127, s204, s209],
  [s5, s20, s109, s129, s204, s209],
  [s5, s20, s109, s153, s183, s204],
  [s20, s39, s90, s109, s124, s209],
  [s20, s39, s90, s109, s127, s209],
  [s20, s39, s90, s109, s153, s183],
  [s20, s109, s121, s161, s193, s195],
  [s56, s110, s169, s204, s209],
  [s114, s169, s190, s204, s209]]
def b5_28 : List (List Sig) := [
  [s0, s25, s90, s169, s190, s209],
  [s0, s25, s109, s153, s190, s209],
  [s5, s20, s54, s90, s153, s209],
  [s5, s20, s90, s153, s190, s209]]
def b5_29 : List (List Sig) := [
  [s4, s30, s98, s169, s193, s204],
  [s4, s30, s109, s153, s193, s209],
  [s4, s31, s98, s169, s193, s204],
  [s4, s31, s105, s153, s193, s209],
  [s4, s31, s109, s153, s193, s209]]
def b5_30 : List (List Sig) := [
  [s5, s50, s78, s195, s204, s209],
  [s5, s50, s169, s195, s204, s209],
  [s5, s78, s139, s195, s204, s209]]
def bucketTier5 : List (List (List Sig)) := [b5_0, b5_1, [], b5_3, b5_4, b5_5, b5_6, b5_7, b5_8, b5_9, [], [], b5_12, b5_13, b5_14, b5_15, b5_16, b5_17, [], b5_19, [], [], b5_22, [], b5_24, b5_25, b5_26, b5_27, b5_28, b5_29, b5_30]

def b6_0 : List (List Sig) := [
  [s5, s78, s190, s204, s209],
  [s5, s86, s169, s204, s209],
  [s6, s20, s39, s98, s109, s139, s204],
  [s20, s39, s41, s98, s109, s139, s204],
  [s20, s39, s43, s98, s109, s139, s204]]
def b6_1 : List (List Sig) := [
  [s5, s20, s55, s72, s204, s209],
  [s5, s20, s57, s98, s169, s204, s209],
  [s5, s20, s57, s109, s161, s204, s209],
  [s5, s20, s81, s109, s175, s204, s209],
  [s5, s20, s90, s139, s169, s204, s209],
  [s5, s20, s90, s169, s182, s204, s209],
  [s5, s20, s90, s169, s194, s204, s209],
  [s5, s20, s109, s139, s153, s204, s209],
  [s5, s20, s109, s153, s182, s204, s209],
  [s5, s20, s109, s153, s194, s204, s209],
  [s5, s20, s109, s169, s180, s204, s209],
  [s5, s39, s109, s125, s144, s204, s209],
  [s5, s39, s109, s125, s169, s204, s209],
  [s5, s39, s109, s144, s153, s204, s209],
  [s15, s39, s109, s123, s209, s211],
  [s19, s37, s109, s169, s193, s195],
  [s19, s39, s109, s167, s193, s195],
  [s19, s39, s109, s169, s193, s195],
  [s20, s25, s70, s109, s169, s209],
  [s20, s25, s72, s109, s139, s204, s209],
  [s20, s25, s72, s109, s182, s204, s209],
  [s20, s25, s98, s109, s169, s182, s204],
  [s20, s25, s109, s142, s204, s209],
  [s20, s37, s109, s169, s193, s195],
  [s20, s39, s57, s98, s109, s161, s204],
  [s20, s39, s90, s109, s139, s153, s209],
  [s20, s39, s90, s109, s153, s182, s209],
  [s20, s39, s107, s169, s193, s195],
  [s20, s39, s109, s153, s179, s209],
  [s20, s39, s109, s167, s193, s195],
  [s36, s39, s109, s123, s153, s209],
  [s39, s61, s94, s109, s169, s204, s209]]
def b6_2 : List (List Sig) := [
  [s5, s20, s25, s72, s193, s204, s209],
  [s5, s20, s25, s109, s153, s193, s209],
  [s5, s20, s39, s90, s153, s193, s209],
  [s20, s25, s39, s72, s90, s193, s209]]
def b6_3 : List (List Sig) := [
  [s5, s20, s57, s72, s204, s209],
  [s5, s20, s116, s153, s193, s204, s209],
  [s5, s20, s117, s153, s193, s204, s209],
  [s5, s20, s119, s153, s193, s204, s209],
  [s5, s20, s120, s153, s193, s204, s209],
  [s5, s21, s109, s169, s175, s204, s209],
  [s5, s78, s175, s204, s209],
  [s18, s20, s25, s90, s169, s193, s209],
  [s18, s20, s25, s109, s153, s193, s209],
  [s18, s20, s39, s90, s153, s193, s209],
  [s20, s25, s32, s72, s193, s204, s209],
  [s20, s25, s32, s109, s153, s193, s209],
  [s20, s25, s55, s109, s153, s209],
  [s20, s25, s72, s120, s193, s204, s209],
  [s20, s25, s72, s122, s193, s204, s209],
  [s20, s25, s109, s116, s153, s193, s209],
  [s20, s25, s109, s117, s153, s193, s209],
  [s20, s25, s109, s119, s153, s193, s209],
  [s20, s25, s109, s122, s153, s193, s209],
  [s20, s32, s39, s90, s153, s193, s209],
  [s20, s39, s73, s109, s175, s204, s209],
  [s20, s39, s90, s117, s153, s193, s209],
  [s20, s39, s90, s122, s153, s193, s209],
  [s20, s39, s109, s139, s203, s204, s209]]
def b6_4 : List (List Sig) := [
  [s5, s20, s66, s109, s169, s204, s209],
  [s5, s39, s75, s161, s193, s204, s209],
  [s8, s31, s72, s169, s193, s204, s209],
  [s8, s31, s109, s161, s169, s193, s204],
  [s8, s39, s72, s161, s193, s204, s209],
  [s20, s25, s109, s123, s153, s209],
  [s20, s39, s66, s72, s109, s204, s209],
  [s20, s39, s66, s98, s109, s169, s204],
  [s20, s104, s109, s169, s182, s204]]
def b6_5 : List (List Sig) := [
  [s20, s39, s91, s109, s139, s204, s209],
  [s20, s39, s92, s109, s139, s204, s209],
  [s20, s39, s106, s109, s139, s204, s209],
  [s39, s109, s124, s143, s195, s209]]
def b6_6 : List (List Sig) := [
  [s0, s5, s78, s193, s204, s209],
  [s0, s5, s87, s169, s204, s209],
  [s0, s5, s97, s169, s193, s209],
  [s0, s112, s169, s190, s204, s209],
  [s5, s20, s72, s193, s204, s209],
  [s5, s20, s73, s193, s204, s209],
  [s5, s20, s75, s193, s204, s209],
  [s5, s20, s76, s193, s204, s209],
  [s5, s39, s109, s124, s169, s204, s209],
  [s5, s39, s109, s127, s169, s204, s209],
  [s5, s78, s169, s190, s204, s209],
  [s5, s114, s169, s193, s204, s209],
  [s8, s20, s72, s193, s204, s209],
  [s14, s20, s72, s193, s204, s209],
  [s20, s109, s121, s161, s193, s204, s209],
  [s20, s109, s121, s169, s193, s195, s209],
  [s39, s61, s109, s153, s193, s195, s209],
  [s39, s109, s118, s153, s193, s195, s209]]
def b6_7 : List (List Sig) := [
  [s0, s2, s39, s109, s153, s193, s209],
  [s0, s5, s25, s90, s169, s193, s209],
  [s0, s5, s25, s109, s153, s193, s209],
  [s0, s25, s109, s169, s190, s204, s209],
  [s0, s39, s109, s153, s190, s204, s209],
  [s5, s20, s54, s109, s153, s204, s209],
  [s5, s20, s90, s169, s190, s204, s209],
  [s5, s20, s109, s153, s190, s204, s209],
  [s5, s39, s109, s141, s161, s204, s209],
  [s20, s39, s54, s90, s109, s153, s209],
  [s20, s102, s109, s153, s193, s195, s209],
  [s39, s109, s168, s169, s190, s204, s209]]
def b6_8 : List (List Sig) := [
  [s4, s30, s109, s169, s193, s204, s209],
  [s4, s31, s105, s169, s193, s204, s209],
  [s4, s31, s109, s169, s193, s204, s209],
  [s5, s39, s109, s153, s193, s208, s209],
  [s15, s36, s109, s153, s193, s209],
  [s15, s39, s105, s153, s193, s209],
  [s15, s39, s109, s153, s193, s208],
  [s17, s39, s109, s153, s193, s209],
  [s20, s25, s109, s153, s193, s209],
  [s20, s25, s109, s155, s193, s209],
  [s20, s25, s109, s158, s193, s209],
  [s20, s26, s109, s153, s193, s209],
  [s20, s34, s109, s153, s193, s209],
  [s20, s45, s109, s153, s193, s209],
  [s20, s62, s109, s153, s193, s209],
  [s20, s109, s121, s153, s193, s209]]
def b6_9 : List (List Sig) := [
  [s5, s20, s109, s141, s204, s209],
  [s5, s78, s169, s175, s204, s209],
  [s5, s112, s139, s169, s195, s204, s209],
  [s20, s25, s69, s109, s169, s209],
  [s20, s25, s109, s139, s195, s209],
  [s39, s50, s78, s109, s195, s204, s209],
  [s39, s50, s109, s169, s195, s204, s209],
  [s39, s78, s109, s139, s195, s204, s209]]
def b6_10 : List (List Sig) := [
  [s4, s36, s109, s153, s193, s209],
  [s4, s39, s109, s153, s193, s209],
  [s5, s20, s109, s153, s175, s204, s209],
  [s5, s36, s109, s153, s193, s209],
  [s5, s39, s109, s153, s193, s208],
  [s20, s25, s59, s72, s109, s204, s209],
  [s20, s25, s72, s109, s175, s204, s209],
  [s20, s25, s109, s139, s193, s195, s209]]
def b6_11 : List (List Sig) := [
  [s0, s15, s39, s109, s139, s204, s209],
  [s0, s20, s25, s109, s139, s204, s209],
  [s0, s20, s39, s90, s139, s204, s209],
  [s5, s15, s20, s109, s139, s204, s209],
  [s5, s20, s72, s193, s195, s204, s209],
  [s5, s20, s90, s161, s193, s204, s209],
  [s5, s20, s109, s153, s193, s195, s209],
  [s5, s39, s109, s153, s161, s193, s195],
  [s7, s39, s72, s98, s139, s204],
  [s15, s20, s39, s90, s109, s139, s209],
  [s20, s25, s72, s98, s193, s204, s209],
  [s20, s25, s72, s109, s193, s195, s209],
  [s20, s25, s98, s109, s153, s193, s209],
  [s20, s25, s98, s109, s161, s193, s204],
  [s20, s25, s109, s141, s204, s209],
  [s20, s39, s90, s109, s161, s193, s195]]
def b6_12 : List (List Sig) := [
  [s32, s39, s109, s153, s161, s193, s195],
  [s36, s109, s123, s153, s209],
  [s39, s109, s119, s153, s161, s193, s195],
  [s39, s109, s123, s153, s208]]
def b6_13 : List (List Sig) := [
  [s5, s20, s90, s153, s193, s209],
  [s5, s111, s169, s193, s204, s209],
  [s20, s25, s72, s90, s193, s209]]
def b6_14 : List (List Sig) := [
  [s5, s20, s85, s153, s193, s204, s209],
  [s5, s24, s85, s153, s169, s204, s209],
  [s5, s110, s153, s169, s193, s204, s209],
  [s19, s37, s109, s139, s204, s209],
  [s19, s39, s109, s138, s204, s209],
  [s19, s39, s109, s139, s204, s209],
  [s20, s25, s85, s109, s153, s193, s209],
  [s20, s37, s109, s139, s204, s209],
  [s20, s39, s107, s139, s204, s209],
  [s20, s39, s109, s139, s195, s212],
  [s20, s104, s109, s161, s193, s204],
  [s36, s39, s109, s153, s182, s209]]
def b6_15 : List (List Sig) := [
  [s5, s11, s109, s144, s204, s209],
  [s5, s20, s72, s139, s204, s209],
  [s5, s20, s72, s194, s204, s209],
  [s5, s20, s109, s144, s204, s209],
  [s5, s20, s109, s169, s180, s209],
  [s5, s20, s120, s161, s193, s204, s209],
  [s5, s39, s53, s109, s169, s193, s195],
  [s5, s56, s112, s169, s204, s209],
  [s14, s61, s109, s169, s204, s209],
  [s20, s39, s96, s109, s204, s209],
  [s39, s61, s76, s109, s204, s209]]
def b6_16 : List (List Sig) := [
  [s0, s39, s58, s109, s169, s204, s209],
  [s5, s19, s109, s167, s193, s204, s209],
  [s5, s19, s109, s169, s193, s204, s209],
  [s5, s20, s58, s109, s169, s204, s209],
  [s5, s20, s72, s193, s204, s209, s212],
  [s5, s20, s107, s169, s193, s204, s209],
  [s5, s20, s109, s167, s193, s204, s209],
  [s5, s20, s109, s169, s179, s204, s209],
  [s5, s20, s109, s169, s193, s195, s212],
  [s5, s39, s109, s123, s153, s209, s211],
  [s5, s39, s109, s140, s169, s204, s209],
  [s14, s72, s169, s185, s204, s209],
  [s19, s37, s72, s109, s193, s204, s209],
  [s19, s39, s71, s109, s193, s204, s209],
  [s19, s39, s72, s109, s193, s204, s209],
  [s20, s37, s72, s109, s193, s204, s209],
  [s20, s39, s72, s109, s179, s204, s209],
  [s20, s39, s72, s109, s193, s195, s212],
  [s20, s39, s72, s190, s204, s209],
  [s20, s39, s90, s109, s142, s204, s209],
  [s20, s39, s107, s109, s169, s193, s195],
  [s39, s109, s150, s169, s193, s195]]
def b6_17 : List (List Sig) := [
  [s20, s25, s109, s139, s153, s209],
  [s20, s25, s109, s153, s182, s209],
  [s39, s64, s78, s109, s182, s204, s209],
  [s39, s64, s109, s169, s182, s204, s209],
  [s39, s78, s109, s153, s182, s204, s209]]
def b6_18 : List (List Sig) := [
  [s3, s5, s20, s72, s193, s204, s209],
  [s3, s5, s20, s109, s161, s193, s204],
  [s5, s6, s20, s72, s193, s204, s209],
  [s5, s6, s20, s98, s169, s193, s204],
  [s5, s7, s20, s72, s193, s204, s209],
  [s5, s7, s20, s98, s169, s193, s204],
  [s5, s7, s20, s109, s161, s193, s204],
  [s5, s7, s39, s72, s161, s193, s204],
  [s5, s20, s41, s72, s193, s204, s209],
  [s5, s20, s41, s98, s169, s193, s204],
  [s5, s20, s43, s72, s193, s204, s209],
  [s5, s20, s43, s98, s169, s193, s204],
  [s5, s20, s43, s109, s161, s193, s204],
  [s5, s20, s55, s90, s169, s204, s209],
  [s5, s20, s55, s109, s153, s204, s209],
  [s6, s20, s39, s72, s98, s193, s204],
  [s7, s20, s39, s72, s98, s193, s204],
  [s20, s25, s55, s72, s109, s204, s209],
  [s20, s25, s55, s90, s109, s169, s209],
  [s20, s25, s109, s153, s182, s193, s209],
  [s20, s39, s55, s90, s109, s153, s209]]
def b6_19 : List (List Sig) := [
  [s5, s15, s109, s123, s169, s204, s209],
  [s5, s20, s72, s153, s193, s204, s209],
  [s5, s20, s90, s153, s169, s193, s209],
  [s5, s20, s109, s123, s153, s204, s209],
  [s15, s39, s72, s109, s123, s204, s209],
  [s20, s25, s72, s90, s169, s193, s209],
  [s20, s25, s72, s109, s153, s193, s209],
  [s20, s25, s109, s154, s193, s209],
  [s20, s34, s109, s169, s175, s209],
  [s20, s39, s90, s109, s123, s153, s209],
  [s20, s45, s109, s169, s175, s209],
  [s20, s62, s109, s169, s175, s209],
  [s20, s109, s121, s169, s175, s209]]
def b6_20 : List (List Sig) := [
  [s5, s20, s57, s109, s153, s204, s209],
  [s20, s39, s108, s109, s139, s204, s209],
  [s20, s102, s109, s139, s195, s204, s209]]
def b6_21 : List (List Sig) := [
  [s5, s20, s72, s190, s204, s209],
  [s5, s78, s193, s195, s204, s209],
  [s20, s25, s109, s139, s204, s209],
  [s20, s25, s109, s145, s204, s209],
  [s20, s25, s109, s146, s204, s209],
  [s20, s25, s109, s148, s204, s209],
  [s20, s26, s109, s139, s204, s209],
  [s20, s28, s109, s139, s204, s209],
  [s20, s34, s109, s139, s204, s209],
  [s20, s45, s109, s139, s204, s209],
  [s20, s109, s121, s139, s204, s209]]
def b6_22 : List (List Sig) := [
  [s20, s25, s109, s123, s209],
  [s20, s39, s109, s124, s204, s209],
  [s20, s39, s109, s127, s204, s209],
  [s20, s39, s109, s129, s204, s209],
  [s20, s39, s109, s153, s183, s204],
  [s38, s39, s109, s169, s171, s204, s209],
  [s110, s169, s190, s204, s209]]
def b6_23 : List (List Sig) := [
  [s0, s2, s112, s169, s193, s204, s209],
  [s0, s5, s97, s169, s193, s204, s209],
  [s0, s5, s112, s153, s193, s204, s209],
  [s5, s15, s109, s153, s193, s209, s211],
  [s5, s20, s81, s109, s182, s204, s209],
  [s5, s20, s90, s169, s193, s204, s209],
  [s5, s20, s91, s169, s193, s204, s209],
  [s5, s20, s93, s169, s193, s204, s209],
  [s5, s20, s94, s169, s193, s204, s209],
  [s5, s20, s95, s169, s193, s204, s209],
  [s5, s20, s103, s169, s193, s204, s209],
  [s5, s20, s109, s153, s193, s204, s209],
  [s5, s20, s109, s155, s193, s204, s209],
  [s5, s20, s109, s157, s193, s204, s209],
  [s5, s20, s109, s160, s193, s204, s209],
  [s5, s20, s109, s163, s193, s204, s209],
  [s5, s21, s109, s153, s193, s204, s209],
  [s5, s33, s109, s153, s193, s204, s209],
  [s5, s39, s75, s153, s193, s204, s209],
  [s5, s39, s76, s153, s193, s204, s209],
  [s5, s112, s153, s169, s190, s204, s209],
  [s8, s20, s90, s169, s193, s204, s209],
  [s8, s20, s109, s153, s193, s204, s209],
  [s8, s39, s72, s153, s193, s204, s209],
  [s14, s20, s109, s153, s193, s204, s209],
  [s15, s39, s63, s109, s193, s209, s211],
  [s15, s39, s83, s109, s193, s209],
  [s15, s39, s105, s109, s153, s193, s209],
  [s20, s25, s54, s109, s153, s209],
  [s20, s25, s72, s109, s193, s204, s209],
  [s20, s25, s73, s109, s193, s204, s209],
  [s20, s25, s74, s109, s193, s204, s209],
  [s20, s25, s75, s109, s193, s204, s209],
  [s20, s25, s76, s109, s193, s204, s209],
  [s20, s25, s84, s109, s193, s209],
  [s20, s25, s109, s162, s193, s204, s209],
  [s20, s26, s72, s109, s193, s204, s209],
  [s20, s26, s90, s109, s169, s193, s209],
  [s20, s28, s72, s109, s193, s204, s209],
  [s20, s28, s90, s109, s169, s193, s209],
  [s20, s39, s72, s93, s193, s204, s209],
  [s20, s39, s72, s193, s198, s204, s209],
  [s20, s39, s75, s90, s193, s204, s209],
  [s20, s39, s90, s109, s153, s193, s209],
  [s20, s39, s90, s109, s155, s193, s209],
  [s20, s39, s90, s109, s160, s193, s209],
  [s20, s39, s90, s162, s193, s204, s209],
  [s20, s39, s91, s109, s153, s193, s209],
  [s20, s39, s93, s109, s153, s193, s209],
  [s20, s39, s94, s109, s153, s193, s209],
  [s20, s39, s95, s109, s153, s193, s209],
  [s20, s39, s103, s109, s153, s193, s209]]
def b6_24 : List (List Sig) := [
  [s5, s20, s72, s175, s204, s209],
  [s5, s20, s109, s139, s195, s204, s209],
  [s5, s20, s109, s169, s178, s204, s209],
  [s5, s39, s109, s144, s195, s204, s209],
  [s20, s25, s72, s109, s175, s209],
  [s20, s25, s98, s109, s139, s204, s209],
  [s20, s39, s72, s109, s178, s204, s209],
  [s20, s39, s90, s109, s139, s195, s209]]
def b6_25 : List (List Sig) := [
  [s5, s20, s173, s193, s204, s209],
  [s5, s21, s109, s169, s182, s204, s209],
  [s5, s50, s78, s204, s209],
  [s5, s50, s169, s204, s209],
  [s5, s78, s139, s204, s209],
  [s10, s39, s109, s143, s195, s204, s209],
  [s20, s39, s73, s109, s182, s204, s209],
  [s36, s109, s153, s182, s209],
  [s39, s109, s138, s167, s195],
  [s39, s109, s139, s167, s195]]
def b6_26 : List (List Sig) := [
  [s5, s15, s63, s169, s193, s204, s209],
  [s5, s15, s72, s153, s193, s204, s209],
  [s5, s20, s90, s139, s204, s209],
  [s5, s61, s119, s169, s204, s209],
  [s12, s39, s90, s98, s169, s193],
  [s15, s39, s72, s90, s153, s193, s209],
  [s20, s25, s59, s109, s153, s209],
  [s20, s39, s90, s109, s141, s204, s209],
  [s20, s109, s153, s193, s207, s209]]
def b6_27 : List (List Sig) := [
  [s5, s78, s169, s193, s195, s204, s209],
  [s5, s112, s153, s161, s193, s204, s209],
  [s20, s25, s109, s161, s193, s195],
  [s20, s72, s119, s185, s204, s209],
  [s20, s72, s190, s204, s209],
  [s20, s104, s109, s139, s204, s209],
  [s20, s109, s121, s169, s182, s204, s209],
  [s20, s109, s139, s199, s204, s209],
  [s39, s61, s109, s153, s182, s204, s209],
  [s39, s64, s68, s109, s193, s204, s209],
  [s39, s64, s78, s109, s193, s195, s209],
  [s39, s64, s109, s161, s193, s204, s209],
  [s39, s67, s109, s153, s182, s204, s209],
  [s39, s78, s109, s153, s193, s195, s209],
  [s39, s87, s109, s153, s161, s204, s209],
  [s39, s109, s112, s153, s161, s193, s195],
  [s39, s109, s118, s153, s182, s204, s209]]
def b6_28 : List (List Sig) := [
  [s0, s110, s169, s193, s204, s209],
  [s20, s25, s46, s109, s139, s209],
  [s20, s25, s48, s109, s139, s209],
  [s20, s25, s109, s123, s169, s209],
  [s20, s72, s190, s193, s204, s209],
  [s20, s72, s193, s202, s204, s209],
  [s20, s102, s109, s153, s182, s204, s209],
  [s24, s39, s109, s153, s161, s193, s195],
  [s39, s79, s109, s169, s195]]
def b6_29 : List (List Sig) := [
  [s0, s15, s39, s90, s169, s193, s209],
  [s0, s20, s25, s90, s169, s193, s209],
  [s0, s20, s25, s109, s153, s193, s209],
  [s0, s20, s39, s90, s153, s193, s209],
  [s4, s36, s109, s169, s182, s204, s209],
  [s4, s39, s109, s169, s182, s204, s209],
  [s5, s15, s20, s72, s193, s204, s209],
  [s5, s15, s20, s90, s169, s193, s209],
  [s5, s20, s89, s109, s204, s209],
  [s5, s36, s109, s169, s182, s204, s209],
  [s5, s39, s109, s138, s167, s204, s209],
  [s5, s39, s109, s139, s167, s204, s209],
  [s5, s39, s109, s139, s169, s195, s212],
  [s5, s39, s109, s143, s195, s204, s209],
  [s5, s64, s78, s193, s204, s209],
  [s5, s64, s169, s193, s204, s209],
  [s5, s78, s153, s193, s204, s209],
  [s5, s87, s153, s169, s204, s209],
  [s15, s20, s39, s72, s90, s193, s209],
  [s20, s39, s107, s109, s139, s204, s209]]
def b6_30 : List (List Sig) := [
  [s20, s25, s46, s72, s109, s193, s209],
  [s20, s25, s48, s72, s109, s193, s209],
  [s20, s25, s109, s135, s204, s209]]
def bucketTier6 : List (List (List Sig)) := [b6_0, b6_1, b6_2, b6_3, b6_4, b6_5, b6_6, b6_7, b6_8, b6_9, b6_10, b6_11, b6_12, b6_13, b6_14, b6_15, b6_16, b6_17, b6_18, b6_19, b6_20, b6_21, b6_22, b6_23, b6_24, b6_25, b6_26, b6_27, b6_28, b6_29, b6_30]

def b7_0 : List (List Sig) := [
  [s0, s39, s109, s169, s190, s204, s209],
  [s5, s20, s109, s169, s190, s204, s209],
  [s5, s119, s169, s185, s204, s209],
  [s9, s25, s109, s139, s169, s204, s209],
  [s20, s39, s109, s156, s193, s204, s209],
  [s20, s39, s109, s169, s193, s203, s204, s209],
  [s38, s39, s109, s169, s193, s195, s204, s209],
  [s39, s56, s109, s169, s190, s204, s209],
  [s39, s78, s109, s193, s195, s204, s209],
  [s39, s109, s113, s169, s204, s209]]
def b7_1 : List (List Sig) := [
  [s5, s24, s85, s169, s204, s209],
  [s5, s110, s169, s193, s204, s209],
  [s20, s39, s109, s123, s204, s209],
  [s39, s109, s169, s191, s204, s209]]
def b7_2 : List (List Sig) := [
  [s5, s39, s109, s153, s169, s193, s204, s209],
  [s5, s39, s109, s155, s169, s193, s204, s209],
  [s5, s39, s109, s158, s169, s193, s204, s209],
  [s5, s39, s109, s166, s169, s193, s204, s209],
  [s8, s39, s109, s153, s169, s193, s204, s209],
  [s14, s39, s109, s153, s169, s193, s204, s209],
  [s20, s39, s54, s109, s153, s204, s209],
  [s20, s39, s90, s109, s169, s193, s204, s209],
  [s20, s39, s91, s109, s169, s193, s204, s209],
  [s20, s39, s92, s109, s169, s193, s204, s209],
  [s20, s39, s93, s109, s169, s193, s204, s209],
  [s20, s39, s94, s109, s169, s193, s204, s209],
  [s20, s39, s95, s109, s169, s193, s204, s209],
  [s20, s39, s103, s109, s169, s193, s204, s209],
  [s20, s39, s106, s109, s169, s193, s204, s209],
  [s20, s39, s109, s169, s193, s198, s204, s209],
  [s20, s39, s109, s169, s193, s200, s204, s209]]
def b7_3 : List (List Sig) := [
  [s5, s20, s109, s169, s175, s204, s209],
  [s5, s39, s109, s139, s169, s195, s204, s209],
  [s7, s20, s39, s109, s169, s182, s204],
  [s20, s39, s72, s109, s175, s204, s209],
  [s20, s109, s169, s186, s193, s204, s209],
  [s39, s51, s109, s139, s204, s209]]
def b7_4 : List (List Sig) := [
  [s0, s20, s39, s109, s139, s204, s209],
  [s5, s112, s139, s169, s204, s209],
  [s20, s39, s109, s141, s204, s209],
  [s20, s39, s109, s173, s193, s204, s209],
  [s32, s39, s109, s139, s169, s195, s204, s209],
  [s36, s109, s169, s182, s204, s209],
  [s39, s50, s78, s109, s204, s209],
  [s39, s50, s109, s169, s204, s209],
  [s39, s78, s109, s139, s204, s209],
  [s39, s109, s115, s139, s169, s195, s204, s209],
  [s39, s109, s119, s139, s169, s195, s204, s209],
  [s39, s109, s131, s159, s204, s209],
  [s39, s109, s131, s169, s204, s209],
  [s39, s109, s138, s167, s204, s209],
  [s39, s109, s139, s159, s204, s209],
  [s39, s109, s139, s167, s204, s209],
  [s39, s109, s139, s169, s195, s212],
  [s39, s109, s139, s169, s196, s209],
  [s39, s109, s143, s195, s204, s209]]
def b7_5 : List (List Sig) := [
  [s5, s15, s109, s153, s169, s193, s204, s209],
  [s5, s39, s117, s169, s193, s195, s204, s209],
  [s12, s39, s90, s109, s169, s193, s209],
  [s15, s39, s63, s109, s169, s193, s204, s209],
  [s15, s39, s72, s109, s153, s193, s204, s209],
  [s20, s25, s59, s109, s169, s204, s209],
  [s20, s39, s90, s109, s139, s204, s209],
  [s20, s39, s109, s153, s175, s204, s209],
  [s36, s39, s109, s153, s193, s209],
  [s39, s61, s109, s119, s169, s204, s209]]
def b7_6 : List (List Sig) := [
  [s5, s20, s72, s193, s204, s209],
  [s5, s39, s65, s109, s169, s204, s209],
  [s15, s20, s39, s109, s139, s204, s209],
  [s20, s25, s109, s161, s193, s204, s209],
  [s20, s39, s109, s153, s193, s195, s209],
  [s20, s109, s119, s169, s185, s204, s209],
  [s20, s109, s169, s190, s204, s209],
  [s39, s78, s109, s169, s193, s195, s204, s209],
  [s39, s109, s112, s153, s161, s193, s204, s209]]
def b7_7 : List (List Sig) := [
  [s5, s20, s85, s169, s193, s204, s209],
  [s20, s24, s72, s109, s193, s204, s209],
  [s20, s24, s85, s109, s169, s204, s209],
  [s20, s39, s109, s123, s169, s204, s209],
  [s20, s39, s109, s169, s171, s204, s209],
  [s20, s109, s169, s190, s193, s204, s209],
  [s20, s109, s169, s193, s202, s204, s209],
  [s24, s39, s109, s153, s161, s193, s204, s209]]
def b7_8 : List (List Sig) := [
  [s0, s15, s39, s109, s169, s193, s204, s209],
  [s0, s20, s25, s109, s169, s193, s204, s209],
  [s0, s20, s39, s90, s169, s193, s204, s209],
  [s0, s20, s39, s109, s153, s193, s204, s209],
  [s5, s15, s20, s109, s169, s193, s204, s209],
  [s5, s39, s41, s109, s169, s193, s195, s204],
  [s5, s39, s109, s139, s169, s204, s209, s212],
  [s5, s112, s153, s169, s193, s204, s209],
  [s7, s39, s72, s98, s169, s193, s204],
  [s7, s39, s72, s109, s161, s193, s204],
  [s8, s31, s109, s169, s193, s204, s209],
  [s15, s20, s39, s72, s109, s193, s204, s209],
  [s15, s20, s39, s90, s109, s169, s193, s209],
  [s20, s25, s109, s153, s193, s209],
  [s39, s64, s78, s109, s193, s204, s209],
  [s39, s64, s109, s169, s193, s204, s209],
  [s39, s78, s109, s153, s193, s204, s209],
  [s39, s87, s109, s153, s169, s204, s209]]
def b7_9 : List (List Sig) := [
  [s5, s39, s56, s109, s169, s204, s209],
  [s20, s24, s109, s153, s193, s204, s209],
  [s39, s109, s132, s169, s193, s195, s204]]
def b7_10 : List (List Sig) := [
  [s5, s39, s41, s109, s139, s169, s204, s209],
  [s5, s112, s169, s190, s204, s209],
  [s20, s25, s39, s109, s139, s204, s209],
  [s39, s109, s137, s169, s204, s209],
  [s39, s109, s147, s169, s204, s209],
  [s39, s109, s169, s190, s204, s209]]
def b7_11 : List (List Sig) := [
  [s5, s20, s55, s109, s169, s204, s209],
  [s5, s39, s109, s139, s153, s169, s204, s209],
  [s5, s39, s109, s153, s169, s194, s204, s209],
  [s16, s29, s109, s169, s193, s204, s209],
  [s16, s39, s109, s164, s193, s204, s209],
  [s16, s39, s109, s169, s193, s204, s209],
  [s19, s37, s109, s169, s193, s204, s209],
  [s19, s39, s109, s167, s193, s204, s209],
  [s19, s39, s109, s169, s193, s204, s209],
  [s20, s29, s109, s169, s193, s204, s209],
  [s20, s37, s109, s169, s193, s204, s209],
  [s20, s39, s55, s72, s109, s204, s209],
  [s20, s39, s57, s98, s109, s169, s204, s209],
  [s20, s39, s90, s109, s139, s169, s204, s209],
  [s20, s39, s90, s109, s169, s182, s204, s209],
  [s20, s39, s107, s169, s193, s204, s209],
  [s20, s39, s109, s164, s193, s204, s209],
  [s20, s39, s109, s167, s193, s204, s209],
  [s20, s39, s109, s169, s179, s204, s209],
  [s20, s39, s109, s169, s189, s204, s209],
  [s20, s39, s109, s169, s193, s195, s212],
  [s20, s39, s109, s169, s193, s201, s209],
  [s35, s39, s109, s139, s169, s204, s209],
  [s39, s109, s132, s139, s169, s204, s209]]
def b7_12 : List (List Sig) := [
  [s5, s20, s25, s109, s169, s193, s204, s209],
  [s5, s20, s39, s90, s169, s193, s204, s209],
  [s5, s20, s39, s109, s153, s193, s204, s209],
  [s5, s20, s72, s169, s193, s204, s209],
  [s5, s39, s132, s169, s193, s204, s209],
  [s20, s25, s39, s72, s109, s193, s204, s209],
  [s39, s109, s124, s169, s204, s209],
  [s39, s109, s127, s169, s204, s209]]
def b7_13 : List (List Sig) := [
  [s5, s20, s57, s109, s169, s204, s209],
  [s5, s39, s116, s153, s169, s193, s204, s209],
  [s5, s39, s117, s153, s169, s193, s204, s209],
  [s5, s39, s119, s153, s169, s193, s204, s209],
  [s7, s20, s39, s109, s161, s193, s204],
  [s18, s20, s25, s109, s169, s193, s204, s209],
  [s18, s20, s39, s90, s169, s193, s204, s209],
  [s18, s20, s39, s109, s153, s193, s204, s209],
  [s20, s25, s32, s109, s169, s193, s204, s209],
  [s20, s25, s55, s109, s169, s204, s209],
  [s20, s25, s109, s117, s169, s193, s204, s209],
  [s20, s25, s109, s119, s169, s193, s204, s209],
  [s20, s25, s109, s122, s169, s193, s204, s209],
  [s20, s32, s39, s90, s169, s193, s204, s209],
  [s20, s32, s39, s109, s153, s193, s204, s209],
  [s20, s39, s43, s109, s161, s193, s204],
  [s20, s39, s55, s109, s153, s204, s209],
  [s20, s39, s57, s72, s109, s204, s209],
  [s20, s39, s90, s117, s169, s193, s204, s209],
  [s20, s39, s90, s122, s169, s193, s204, s209],
  [s20, s39, s109, s116, s153, s193, s204, s209],
  [s20, s39, s109, s117, s153, s193, s204, s209],
  [s20, s39, s109, s119, s153, s193, s204, s209],
  [s20, s39, s109, s120, s153, s193, s204, s209],
  [s23, s109, s169, s175, s204, s209],
  [s35, s39, s109, s169, s182, s204],
  [s39, s78, s109, s175, s204, s209],
  [s39, s109, s141, s161, s204, s209]]
def b7_14 : List (List Sig) := [
  [s5, s20, s81, s109, s193, s204, s209],
  [s8, s39, s109, s161, s169, s193, s204, s209],
  [s15, s39, s109, s123, s169, s204, s209],
  [s20, s25, s47, s109, s169, s193, s209],
  [s20, s25, s109, s153, s169, s193, s209],
  [s20, s39, s109, s123, s153, s204, s209],
  [s20, s39, s109, s139, s204, s209],
  [s20, s39, s109, s145, s204, s209],
  [s20, s39, s109, s148, s204, s209],
  [s33, s39, s109, s139, s204, s209],
  [s39, s44, s109, s139, s204, s209],
  [s39, s61, s109, s139, s204, s209],
  [s39, s109, s118, s139, s204, s209],
  [s39, s109, s153, s193, s208, s209]]
def b7_15 : List (List Sig) := [
  [s20, s39, s57, s109, s153, s204, s209],
  [s20, s102, s109, s139, s204, s209],
  [s20, s109, s139, s197, s204, s209],
  [s39, s56, s109, s169, s204, s209]]
def b7_16 : List (List Sig) := [
  [s0, s5, s112, s169, s193, s204, s209],
  [s5, s20, s109, s169, s193, s204, s209],
  [s5, s21, s109, s169, s193, s204, s209],
  [s5, s33, s109, s169, s193, s204, s209],
  [s5, s39, s75, s169, s193, s204, s209],
  [s5, s39, s76, s169, s193, s204, s209],
  [s5, s78, s193, s204, s209],
  [s5, s87, s169, s204, s209],
  [s8, s20, s109, s169, s193, s204, s209],
  [s8, s39, s72, s169, s193, s204, s209],
  [s14, s20, s109, s169, s193, s204, s209],
  [s14, s39, s72, s169, s193, s204, s209],
  [s20, s39, s72, s109, s193, s204, s209],
  [s20, s39, s73, s109, s193, s204, s209],
  [s20, s39, s75, s109, s193, s204, s209],
  [s20, s39, s76, s109, s193, s204, s209],
  [s20, s39, s109, s162, s193, s204, s209],
  [s36, s109, s153, s193, s209],
  [s39, s61, s109, s169, s193, s195, s204, s209],
  [s39, s109, s118, s169, s193, s195, s204, s209],
  [s39, s109, s153, s193, s208]]
def b7_17 : List (List Sig) := [
  [s0, s2, s39, s109, s169, s193, s204, s209],
  [s0, s5, s25, s109, s169, s193, s204, s209],
  [s0, s5, s39, s109, s153, s193, s204, s209],
  [s5, s39, s54, s109, s153, s169, s204, s209],
  [s5, s39, s109, s153, s169, s190, s204, s209],
  [s5, s39, s109, s168, s169, s193, s204, s209],
  [s20, s39, s108, s109, s169, s193, s204, s209],
  [s20, s39, s109, s169, s192, s204, s209],
  [s20, s102, s109, s169, s193, s195, s204, s209],
  [s39, s109, s153, s161, s193, s195]]
def b7_18 : List (List Sig) := [
  [s15, s39, s109, s153, s193, s209, s211],
  [s20, s25, s109, s169, s193, s204, s209],
  [s20, s26, s109, s169, s193, s204, s209],
  [s20, s28, s109, s169, s193, s204, s209],
  [s20, s34, s109, s169, s193, s204, s209],
  [s20, s39, s81, s109, s182, s204, s209],
  [s20, s39, s109, s153, s193, s204, s209],
  [s20, s39, s109, s155, s193, s204, s209],
  [s20, s39, s109, s157, s193, s204, s209],
  [s20, s39, s109, s158, s193, s204, s209],
  [s20, s39, s109, s160, s193, s204, s209],
  [s20, s39, s109, s163, s193, s204, s209],
  [s20, s45, s109, s169, s193, s204, s209],
  [s20, s62, s109, s169, s193, s204, s209],
  [s20, s109, s121, s169, s193, s204, s209],
  [s21, s39, s109, s153, s193, s204, s209],
  [s33, s39, s109, s153, s193, s204, s209],
  [s39, s44, s109, s153, s193, s204, s209],
  [s39, s61, s109, s153, s193, s204, s209],
  [s39, s109, s118, s153, s193, s204, s209]]
def b7_19 : List (List Sig) := [
  [s0, s39, s109, s139, s204, s209],
  [s5, s20, s109, s139, s204, s209],
  [s5, s39, s41, s109, s169, s175, s204, s209],
  [s5, s39, s109, s141, s169, s204, s209],
  [s5, s39, s109, s144, s204, s209],
  [s20, s39, s109, s139, s195, s204, s209],
  [s20, s39, s109, s169, s178, s204, s209],
  [s20, s102, s109, s153, s193, s204, s209],
  [s20, s109, s153, s185, s193, s204, s209],
  [s20, s109, s153, s193, s197, s204, s209],
  [s20, s109, s153, s193, s204, s206, s209],
  [s39, s60, s109, s169, s204, s209],
  [s39, s78, s109, s169, s175, s204, s209],
  [s39, s109, s112, s139, s169, s195, s204, s209]]
def b7_20 : List (List Sig) := [
  [s4, s36, s109, s169, s193, s204, s209],
  [s4, s39, s109, s169, s193, s204, s209],
  [s5, s36, s109, s169, s193, s204, s209],
  [s5, s39, s55, s109, s169, s195, s204, s209],
  [s5, s39, s109, s153, s193, s209, s211],
  [s5, s39, s109, s167, s193, s204, s209],
  [s9, s39, s109, s169, s193, s195, s204, s209],
  [s14, s109, s169, s185, s204, s209],
  [s20, s24, s109, s169, s175, s204, s209],
  [s20, s39, s109, s139, s193, s195, s204, s209],
  [s21, s39, s109, s169, s182, s204, s209],
  [s24, s39, s109, s139, s169, s195, s204, s209],
  [s39, s44, s109, s169, s182, s204, s209],
  [s39, s67, s109, s169, s182, s204, s209],
  [s39, s109, s132, s169, s175, s204, s209]]
def b7_21 : List (List Sig) := [
  [s5, s20, s109, s169, s193, s195, s204, s209],
  [s5, s39, s109, s153, s161, s193, s204, s209],
  [s7, s39, s72, s109, s139, s204, s209],
  [s7, s39, s98, s109, s139, s169, s204],
  [s20, s25, s98, s109, s169, s193, s204, s209],
  [s20, s25, s109, s139, s204, s209],
  [s20, s39, s72, s109, s193, s195, s204, s209],
  [s20, s39, s82, s109, s193, s204, s209],
  [s20, s39, s90, s109, s161, s193, s204, s209],
  [s39, s53, s109, s169, s193, s195],
  [s39, s117, s169, s190, s204, s209]]
def b7_22 : List (List Sig) := [
  [s5, s7, s39, s98, s169, s193, s204],
  [s5, s78, s169, s193, s204, s209],
  [s9, s25, s109, s169, s193, s204, s209],
  [s20, s25, s109, s139, s193, s204, s209],
  [s32, s39, s109, s153, s161, s193, s204, s209],
  [s39, s109, s119, s153, s161, s193, s204, s209],
  [s39, s109, s123, s153, s209, s211],
  [s39, s109, s123, s169, s204, s209],
  [s39, s109, s126, s169, s204, s209],
  [s39, s109, s128, s169, s204, s209],
  [s39, s109, s130, s169, s204, s209],
  [s39, s109, s133, s169, s204, s209],
  [s39, s109, s139, s154, s204, s209]]
def b7_23 : List (List Sig) := [
  [s5, s20, s90, s169, s193, s204, s209],
  [s5, s20, s109, s153, s193, s204, s209],
  [s20, s25, s72, s109, s193, s204, s209],
  [s20, s39, s90, s109, s153, s193, s209],
  [s39, s109, s119, s153, s169, s185, s204, s209]]
def b7_24 : List (List Sig) := [
  [s5, s24, s109, s153, s169, s193, s204, s209],
  [s20, s25, s85, s109, s169, s193, s204, s209],
  [s20, s39, s85, s109, s153, s193, s204, s209],
  [s20, s39, s89, s109, s204, s209],
  [s20, s39, s109, s139, s204, s209, s212],
  [s20, s104, s109, s169, s193, s204, s209],
  [s20, s109, s169, s193, s199, s204, s209],
  [s24, s39, s85, s109, s153, s169, s204, s209],
  [s36, s39, s109, s169, s182, s204, s209]]
def b7_25 : List (List Sig) := [
  [s0, s39, s109, s139, s169, s204, s209],
  [s5, s20, s109, s139, s169, s204, s209],
  [s5, s20, s109, s169, s194, s204, s209],
  [s5, s39, s109, s144, s169, s204, s209],
  [s13, s39, s109, s169, s193, s195, s204, s209],
  [s20, s25, s46, s109, s169, s193, s209],
  [s20, s25, s48, s109, s169, s193, s209],
  [s20, s39, s72, s109, s139, s204, s209],
  [s20, s39, s109, s120, s161, s193, s204, s209],
  [s39, s77, s109, s169, s204, s209],
  [s39, s109, s134, s153, s169, s193, s204, s209]]
def b7_26 : List (List Sig) := [
  [s5, s20, s39, s72, s193, s204, s209],
  [s5, s20, s109, s169, s193, s204, s209, s212],
  [s5, s39, s109, s167, s169, s193, s204, s209],
  [s6, s20, s39, s109, s139, s204, s209],
  [s7, s20, s39, s109, s139, s204, s209],
  [s20, s39, s41, s109, s139, s204, s209],
  [s20, s39, s43, s109, s139, s204, s209],
  [s20, s39, s72, s109, s193, s204, s209, s212],
  [s20, s39, s107, s109, s169, s193, s204, s209],
  [s20, s39, s109, s169, s190, s204, s209]]
def b7_27 : List (List Sig) := [
  [s5, s20, s117, s169, s193, s204, s209],
  [s5, s20, s119, s169, s193, s204, s209],
  [s5, s20, s120, s169, s193, s204, s209],
  [s7, s39, s109, s135, s169, s204],
  [s15, s39, s109, s139, s169, s204, s209],
  [s20, s25, s109, s139, s169, s204, s209],
  [s20, s25, s109, s169, s182, s204, s209],
  [s20, s32, s39, s72, s193, s204, s209],
  [s20, s39, s57, s109, s161, s204, s209],
  [s20, s39, s72, s119, s193, s204, s209],
  [s20, s39, s72, s120, s193, s204, s209],
  [s20, s39, s81, s109, s175, s204, s209],
  [s20, s39, s109, s139, s153, s204, s209],
  [s20, s39, s109, s153, s182, s204, s209]]
def b7_28 : List (List Sig) := [
  [s3, s5, s20, s109, s169, s193, s204, s209],
  [s3, s5, s39, s109, s161, s169, s193, s204],
  [s5, s6, s20, s109, s169, s193, s204, s209],
  [s5, s7, s20, s109, s169, s193, s204, s209],
  [s5, s7, s39, s72, s169, s193, s204, s209],
  [s5, s7, s39, s109, s161, s169, s193, s204],
  [s5, s20, s41, s109, s169, s193, s204, s209],
  [s5, s20, s43, s109, s169, s193, s204, s209],
  [s5, s39, s55, s109, s153, s169, s204, s209],
  [s6, s20, s39, s72, s109, s193, s204, s209],
  [s6, s20, s39, s98, s109, s169, s193, s204],
  [s7, s20, s39, s72, s109, s193, s204, s209],
  [s7, s20, s39, s98, s109, s169, s193, s204],
  [s20, s25, s39, s109, s153, s193, s209],
  [s20, s25, s109, s169, s182, s193, s204, s209],
  [s20, s39, s41, s72, s109, s193, s204, s209],
  [s20, s39, s41, s98, s109, s169, s193, s204],
  [s20, s39, s43, s72, s109, s193, s204, s209],
  [s20, s39, s43, s98, s109, s169, s193, s204],
  [s20, s39, s55, s90, s109, s169, s204, s209],
  [s20, s39, s65, s109, s169, s204, s209],
  [s20, s39, s109, s153, s182, s193, s204, s209]]
def b7_29 : List (List Sig) := [
  [s5, s20, s109, s153, s169, s193, s204, s209],
  [s5, s39, s109, s123, s153, s169, s204, s209],
  [s7, s39, s72, s109, s169, s182, s204],
  [s9, s39, s109, s139, s169, s195, s204, s209],
  [s20, s25, s72, s109, s169, s193, s204, s209],
  [s20, s27, s109, s169, s193, s204, s209],
  [s20, s39, s72, s109, s153, s193, s204, s209],
  [s20, s39, s90, s109, s153, s169, s193, s209],
  [s20, s39, s109, s154, s193, s204, s209],
  [s20, s39, s109, s169, s175, s204, s209],
  [s20, s39, s109, s169, s176, s204, s209],
  [s20, s39, s109, s169, s177, s204, s209],
  [s20, s39, s109, s169, s181, s204, s209],
  [s20, s39, s109, s169, s187, s204, s209],
  [s20, s39, s109, s169, s188, s204, s209],
  [s21, s39, s109, s169, s175, s204, s209],
  [s33, s39, s109, s169, s175, s204, s209],
  [s35, s39, s109, s161, s169, s193, s204],
  [s39, s44, s109, s169, s175, s204, s209],
  [s39, s61, s109, s169, s175, s204, s209],
  [s39, s109, s118, s169, s175, s204, s209]]
def b7_30 : List (List Sig) := [
  [s20, s39, s66, s109, s169, s204, s209],
  [s20, s102, s109, s169, s175, s204, s209],
  [s20, s109, s169, s174, s175, s204, s209],
  [s20, s109, s169, s175, s185, s204, s209],
  [s20, s109, s169, s175, s197, s204, s209],
  [s20, s109, s169, s175, s204, s206, s209],
  [s39, s44, s109, s161, s193, s204, s209]]
def bucketTier7 : List (List (List Sig)) := [b7_0, b7_1, b7_2, b7_3, b7_4, b7_5, b7_6, b7_7, b7_8, b7_9, b7_10, b7_11, b7_12, b7_13, b7_14, b7_15, b7_16, b7_17, b7_18, b7_19, b7_20, b7_21, b7_22, b7_23, b7_24, b7_25, b7_26, b7_27, b7_28, b7_29, b7_30]

def b8_0 : List (List Sig) := [
  [s5, s39, s117, s169, s193, s204, s209],
  [s5, s39, s119, s169, s193, s204, s209],
  [s12, s39, s109, s169, s193, s204, s209],
  [s15, s39, s109, s153, s169, s193, s204, s209],
  [s39, s51, s109, s169, s193, s204, s209]]
def b8_1 : List (List Sig) := [
  [s0, s20, s39, s109, s169, s193, s204, s209],
  [s3, s5, s39, s109, s169, s193, s204, s209],
  [s5, s7, s39, s109, s169, s193, s204, s209],
  [s5, s39, s41, s109, s169, s193, s204, s209],
  [s39, s78, s109, s169, s193, s204, s209],
  [s39, s109, s123, s139, s169, s204, s209],
  [s39, s109, s159, s169, s193, s204, s209],
  [s39, s109, s167, s169, s193, s204, s209]]
def b8_2 : List (List Sig) := [
  [s5, s39, s109, s153, s169, s193, s204, s209],
  [s20, s24, s109, s169, s193, s204, s209],
  [s20, s39, s42, s109, s169, s193, s204, s209],
  [s20, s39, s90, s109, s169, s193, s204, s209],
  [s35, s39, s109, s169, s193, s204, s209],
  [s39, s109, s132, s169, s193, s204, s209]]
def b8_3 : List (List Sig) := [
  [s7, s39, s109, s161, s169, s193, s204],
  [s15, s20, s39, s109, s169, s193, s204, s209],
  [s32, s39, s109, s153, s169, s193, s204, s209],
  [s39, s55, s109, s153, s169, s204, s209],
  [s39, s109, s116, s153, s169, s193, s204, s209],
  [s39, s109, s117, s153, s169, s193, s204, s209],
  [s39, s109, s119, s153, s169, s193, s204, s209]]
def b8_4 : List (List Sig) := [
  [s5, s39, s109, s169, s190, s204, s209],
  [s39, s109, s123, s153, s169, s204, s209],
  [s39, s109, s139, s169, s204, s209],
  [s39, s109, s145, s169, s204, s209],
  [s39, s109, s148, s169, s204, s209]]
def b8_5 : List (List Sig) := [
  [s5, s20, s39, s109, s169, s193, s204, s209]]
def b8_6 : List (List Sig) := [
  [s18, s20, s39, s109, s169, s193, s204, s209],
  [s20, s32, s39, s109, s169, s193, s204, s209],
  [s20, s39, s55, s109, s169, s204, s209],
  [s20, s39, s109, s117, s169, s193, s204, s209],
  [s20, s39, s109, s119, s169, s193, s204, s209],
  [s20, s39, s109, s120, s169, s193, s204, s209]]
def b8_7 : List (List Sig) := [
  [s20, s25, s39, s109, s169, s193, s204, s209]]
def b8_8 : List (List Sig) := [
  [s20, s39, s57, s109, s169, s204, s209],
  [s39, s109, s117, s169, s175, s204, s209],
  [s39, s109, s153, s169, s193, s204, s209],
  [s39, s109, s155, s169, s193, s204, s209],
  [s39, s109, s158, s169, s193, s204, s209]]
def b8_9 : List (List Sig) := [
  [s20, s39, s81, s109, s193, s204, s209],
  [s39, s109, s139, s169, s195, s204, s209]]
def b8_10 : List (List Sig) := [
  [s0, s5, s39, s109, s169, s193, s204, s209],
  [s39, s109, s119, s169, s185, s204, s209],
  [s39, s109, s139, s169, s193, s195, s204, s209],
  [s39, s109, s169, s190, s204, s209]]
def b8_11 : List (List Sig) := [
  [s1, s39, s109, s169, s193, s204, s209],
  [s5, s24, s109, s169, s193, s204, s209],
  [s20, s39, s109, s169, s193, s204, s209],
  [s21, s39, s109, s169, s193, s204, s209],
  [s24, s39, s85, s109, s169, s204, s209],
  [s33, s39, s109, s169, s193, s204, s209],
  [s39, s44, s109, s169, s193, s204, s209],
  [s39, s61, s109, s169, s193, s204, s209],
  [s39, s109, s118, s169, s193, s204, s209],
  [s39, s109, s165, s169, s193, s204, s209],
  [s39, s109, s169, s190, s193, s204, s209]]
def b8_12 : List (List Sig) := [
  [s7, s39, s98, s109, s169, s193, s204],
  [s20, s102, s109, s169, s193, s204, s209],
  [s20, s109, s169, s185, s193, s204, s209],
  [s20, s109, s169, s193, s197, s204, s209],
  [s39, s65, s109, s169, s204, s209],
  [s39, s109, s134, s169, s193, s204, s209]]
def b8_14 : List (List Sig) := [
  [s20, s39, s109, s139, s204, s209],
  [s39, s41, s109, s169, s193, s195, s204],
  [s39, s109, s112, s139, s169, s204, s209],
  [s39, s109, s139, s169, s204, s205, s209],
  [s39, s109, s139, s169, s204, s209, s212]]
def b8_15 : List (List Sig) := [
  [s5, s39, s55, s109, s169, s204, s209],
  [s9, s39, s109, s169, s193, s204, s209],
  [s20, s39, s109, s139, s193, s204, s209],
  [s23, s39, s109, s169, s193, s204, s209],
  [s24, s39, s109, s139, s169, s204, s209],
  [s36, s39, s109, s169, s193, s204, s209]]
def b8_16 : List (List Sig) := [
  [s0, s39, s109, s169, s193, s204, s209],
  [s5, s20, s109, s169, s193, s204, s209],
  [s7, s39, s109, s139, s169, s204, s209],
  [s20, s39, s72, s109, s193, s204, s209],
  [s20, s39, s109, s169, s193, s195, s204, s209],
  [s39, s41, s109, s139, s169, s204, s209]]
def b8_17 : List (List Sig) := [
  [s20, s39, s85, s109, s169, s193, s204, s209],
  [s39, s109, s139, s153, s169, s204, s209]]
def b8_18 : List (List Sig) := [
  [s7, s39, s72, s109, s169, s193, s204, s209],
  [s7, s39, s109, s169, s182, s204],
  [s15, s39, s109, s169, s193, s204, s209],
  [s20, s25, s109, s169, s193, s204, s209],
  [s20, s39, s109, s153, s193, s204, s209],
  [s39, s109, s112, s153, s169, s193, s204, s209]]
def b8_19 : List (List Sig) := [
  [s24, s39, s109, s153, s169, s193, s204, s209],
  [s39, s109, s154, s169, s193, s204, s209]]
def b8_20 : List (List Sig) := [
  [s5, s39, s109, s169, s193, s204, s209],
  [s8, s39, s109, s169, s193, s204, s209],
  [s14, s39, s109, s169, s193, s204, s209],
  [s20, s39, s109, s139, s169, s204, s209]]
def b8_21 : List (List Sig) := [
  [s20, s39, s109, s169, s193, s204, s209, s210],
  [s20, s39, s109, s169, s193, s204, s209, s212]]
def b8_22 : List (List Sig) := [
  [s20, s39, s72, s109, s169, s193, s204, s209],
  [s39, s109, s123, s169, s204, s209]]
def b8_23 : List (List Sig) := [
  [s6, s20, s39, s109, s169, s193, s204, s209],
  [s7, s20, s39, s109, s169, s193, s204, s209],
  [s20, s39, s41, s109, s169, s193, s204, s209],
  [s20, s39, s43, s109, s169, s193, s204, s209],
  [s39, s54, s109, s153, s169, s204, s209],
  [s39, s109, s123, s169, s193, s204, s209],
  [s39, s109, s139, s169, s175, s204, s209]]
def b8_24 : List (List Sig) := [
  [s9, s39, s109, s139, s169, s204, s209],
  [s20, s39, s109, s153, s169, s193, s204, s209],
  [s22, s39, s109, s169, s193, s204, s209]]
def b8_25 : List (List Sig) := [
  [s39, s41, s109, s169, s175, s204, s209],
  [s39, s109, s141, s169, s204, s209]]
def b8_26 : List (List Sig) := [
  [s5, s112, s169, s193, s204, s209],
  [s23, s109, s169, s193, s204, s209],
  [s36, s109, s169, s193, s204, s209],
  [s39, s40, s109, s139, s169, s204, s209],
  [s39, s42, s109, s139, s169, s204, s209],
  [s39, s55, s109, s169, s195, s204, s209],
  [s39, s78, s109, s193, s204, s209],
  [s39, s87, s109, s169, s204, s209],
  [s39, s109, s117, s169, s193, s195, s204, s209],
  [s39, s109, s149, s169, s204, s209],
  [s39, s109, s153, s193, s209, s211],
  [s39, s109, s159, s193, s204, s209],
  [s39, s109, s167, s193, s204, s209]]
def b8_27 : List (List Sig) := [
  [s20, s39, s80, s109, s193, s204, s209],
  [s39, s109, s151, s169, s193, s204, s209],
  [s39, s109, s153, s161, s193, s204, s209]]
def b8_29 : List (List Sig) := [
  [s5, s39, s109, s139, s169, s204, s209],
  [s5, s39, s109, s169, s194, s204, s209],
  [s20, s39, s109, s169, s175, s204, s209]]
def b8_30 : List (List Sig) := [
  [s5, s39, s109, s169, s193, s204, s209, s211],
  [s20, s39, s109, s169, s175, s193, s204, s209],
  [s32, s39, s109, s139, s169, s204, s209],
  [s39, s52, s109, s169, s193, s204, s209],
  [s39, s109, s115, s139, s169, s204, s209],
  [s39, s109, s117, s139, s169, s204, s209],
  [s39, s109, s119, s139, s169, s204, s209]]
def bucketTier8 : List (List (List Sig)) := [b8_0, b8_1, b8_2, b8_3, b8_4, b8_5, b8_6, b8_7, b8_8, b8_9, b8_10, b8_11, b8_12, [], b8_14, b8_15, b8_16, b8_17, b8_18, b8_19, b8_20, b8_21, b8_22, b8_23, b8_24, b8_25, b8_26, b8_27, [], b8_29, b8_30]

def b9_4 : List (List Sig) := [
  [s39, s109, s139, s169, s204, s209]]
def b9_5 : List (List Sig) := [
  [s39, s109, s112, s169, s193, s204, s209],
  [s39, s109, s139, s169, s193, s204, s209],
  [s39, s109, s169, s170, s193, s204, s209],
  [s39, s109, s169, s193, s204, s209, s211]]
def b9_6 : List (List Sig) := [
  [s24, s39, s109, s169, s193, s204, s209]]
def b9_7 : List (List Sig) := [
  [s7, s39, s109, s169, s193, s204, s209],
  [s39, s41, s109, s169, s193, s204, s209]]
def b9_8 : List (List Sig) := [
  [s39, s109, s153, s169, s193, s204, s209]]
def b9_11 : List (List Sig) := [
  [s20, s39, s109, s169, s193, s204, s209]]
def b9_17 : List (List Sig) := [
  [s39, s42, s109, s169, s193, s204, s209]]
def b9_20 : List (List Sig) := [
  [s5, s39, s109, s169, s193, s204, s209]]
def b9_21 : List (List Sig) := [
  [s32, s39, s109, s169, s193, s204, s209],
  [s39, s55, s109, s169, s204, s209],
  [s39, s109, s117, s169, s193, s204, s209],
  [s39, s109, s119, s169, s193, s204, s209]]
def bucketTier9 : List (List (List Sig)) := [[], [], [], [], b9_4, b9_5, b9_6, b9_7, b9_8, [], [], b9_11, [], [], [], [], [], b9_17, [], [], b9_20, b9_21, [], [], [], [], [], [], [], [], []]

def b10_26 : List (List Sig) := [
  [s39, s109, s169, s193, s204, s209]]
def bucketTier10 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], b10_26, [], [], [], []]

def buckets : ℕ → List (List (List Sig))
  | 1 => bucketTier1
  | 2 => bucketTier2
  | 3 => bucketTier3
  | 4 => bucketTier4
  | 5 => bucketTier5
  | 6 => bucketTier6
  | 7 => bucketTier7
  | 8 => bucketTier8
  | 9 => bucketTier9
  | 10 => bucketTier10
  | _ => []

def tiers (n : ℕ) : List (List Sig) := (buckets n).flatten
def lookup (n : ℕ) (w : List Sig) : Bool := bucketHas w (buckets n) (hashBucket w)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma lookup_sound (n : ℕ) (w : List Sig) (h : lookup n w = true) : w ∈ tiers n :=
  bucketHas_sound w _ _ h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma startND : (minorRaw (1 : Fin 7)).Nodup := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma sortedStart : sortSignals (minorRaw (1 : Fin 7)) ∈ tiers 10 := by decide +kernel
end Minor1

namespace Minor5
def group : List PermRows := [
  (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]),
  (#[0, 7, 8, 3, 4, 12, 13, 1, 2, 9, 10, 11, 5, 6, 14, 15, 16, 17, 25, 26, 27, 21, 22, 23, 29, 18, 19, 20, 28, 24], #[0, 1, 2, 3, 9, 10, 6, 7, 11, 4, 5, 8, 12]),
  (#[0, 1, 5, 3, 4, 2, 6, 7, 12, 9, 10, 14, 8, 13, 11, 15, 21, 22, 18, 19, 24, 16, 17, 23, 20, 25, 26, 29, 28, 27], #[0, 1, 6, 7, 4, 8, 2, 3, 5, 9, 11, 10, 12]),
  (#[0, 7, 12, 3, 4, 8, 13, 1, 5, 9, 10, 14, 2, 6, 11, 15, 21, 22, 25, 26, 29, 16, 17, 23, 27, 18, 19, 24, 28, 20], #[0, 1, 6, 7, 9, 11, 2, 3, 10, 4, 8, 5, 12]),
  (#[0, 1, 2, 3, 6, 5, 4, 9, 11, 7, 10, 8, 14, 13, 12, 18, 16, 20, 15, 19, 17, 21, 24, 23, 22, 25, 28, 27, 26, 29], #[0, 4, 2, 5, 1, 3, 6, 8, 7, 9, 10, 11, 12]),
  (#[0, 9, 11, 3, 6, 14, 13, 1, 2, 7, 10, 8, 5, 4, 12, 18, 16, 20, 25, 28, 27, 21, 24, 23, 29, 15, 19, 17, 26, 22], #[0, 4, 2, 5, 9, 10, 6, 8, 11, 1, 3, 7, 12]),
  (#[0, 1, 5, 3, 6, 2, 4, 9, 14, 7, 10, 12, 11, 13, 8, 18, 21, 24, 15, 19, 22, 16, 20, 23, 17, 25, 28, 29, 26, 27], #[0, 4, 6, 8, 1, 7, 2, 5, 3, 9, 11, 10, 12]),
  (#[0, 9, 14, 3, 6, 11, 13, 1, 5, 7, 10, 12, 2, 4, 8, 18, 21, 24, 25, 28, 29, 16, 20, 23, 27, 15, 19, 22, 26, 17], #[0, 4, 6, 8, 9, 11, 2, 5, 10, 1, 7, 3, 12]),
  (#[0, 7, 8, 3, 13, 12, 4, 9, 11, 1, 10, 2, 14, 6, 5, 25, 16, 27, 15, 26, 17, 21, 29, 23, 22, 18, 28, 20, 19, 24], #[0, 9, 2, 10, 1, 3, 6, 11, 7, 4, 5, 8, 12]),
  (#[0, 9, 11, 3, 13, 14, 6, 7, 8, 1, 10, 2, 12, 4, 5, 25, 16, 27, 18, 28, 20, 21, 29, 23, 24, 15, 26, 17, 19, 22], #[0, 9, 2, 10, 4, 5, 6, 11, 8, 1, 3, 7, 12]),
  (#[0, 7, 12, 3, 13, 8, 4, 9, 14, 1, 10, 5, 11, 6, 2, 25, 21, 29, 15, 26, 22, 16, 27, 23, 17, 18, 28, 24, 19, 20], #[0, 9, 6, 11, 1, 7, 2, 10, 3, 4, 8, 5, 12]),
  (#[0, 9, 14, 3, 13, 11, 6, 7, 12, 1, 10, 5, 8, 4, 2, 25, 21, 29, 18, 28, 24, 16, 27, 23, 20, 15, 26, 22, 19, 17], #[0, 9, 6, 11, 4, 8, 2, 10, 5, 1, 7, 3, 12])]
def s0 : Sig := (0x6, 0xffffffffffffe03f)
def s1 : Sig := (0x18, 0xffffffffffffe0cf)
def s2 : Sig := (0x1e, 0xffffffffffffe0ff)
def s3 : Sig := (0x26, 0xffffffffffffe1ff)
def s4 : Sig := (0x36, 0x8a)
def s5 : Sig := (0x36, 0xffffffffffffe0bf)
def s6 : Sig := (0x58, 0xffffffffffffe1ff)
def s7 : Sig := (0x5c, 0x2c)
def s8 : Sig := (0x7e, 0xffffffffffffe1ff)
def s9 : Sig := (0x17e, 0xffffffffffffe1ff)
def s10 : Sig := (0x186, 0xffffffffffffe63f)
def s11 : Sig := (0x1fe, 0xffffffffffffe7ff)
def s12 : Sig := (0x426, 0x0)
def s13 : Sig := (0x47e, 0xffffffffffffe1ff)
def s14 : Sig := (0x586, 0xa)
def s15 : Sig := (0x5fe, 0xffffffffffffe1ff)
def s16 : Sig := (0x682, 0xffffffffffffe213)
def s17 : Sig := (0xf86, 0xffffffffffffe63f)
def s18 : Sig := (0xffe, 0xffffffffffffe7ff)
def s19 : Sig := (0x1180, 0xffffffffffffeecf)
def s20 : Sig := (0x11fe, 0xffffffffffffe1ff)
def s21 : Sig := (0x15b6, 0x8a)
def s22 : Sig := (0x15b6, 0xffffffffffffe0bf)
def s23 : Sig := (0x15c8, 0xffffffffffffe175)
def s24 : Sig := (0x15fe, 0xffffffffffffe1ff)
def s25 : Sig := (0x1fb6, 0xffffffffffffe6bf)
def s26 : Sig := (0x207e, 0xffffffffffffe1ff)
def s27 : Sig := (0x207e, 0xffffffffffffefff)
def s28 : Sig := (0x217e, 0xffffffffffffe5ff)
def s29 : Sig := (0x295c, 0x42c)
def s30 : Sig := (0x297e, 0xffffffffffffe5ff)
def s31 : Sig := (0x2fde, 0xffffffffffffe63f)
def s32 : Sig := (0x3198, 0xffffffffffffeecf)
def s33 : Sig := (0x31fe, 0xffffffffffffefff)
def s34 : Sig := (0x35be, 0xffffffffffffeecf)
def s35 : Sig := (0x35fe, 0xffffffffffffefff)
def s36 : Sig := (0x39dc, 0xffffffffffffeeef)
def s37 : Sig := (0x3dfe, 0x4ae)
def s38 : Sig := (0x3f9e, 0xffffffffffffeeff)
def s39 : Sig := (0x56a2, 0xffffffffffffebd3)
def s40 : Sig := (0x5fa6, 0xffffffffffffefff)
def s41 : Sig := (0x5ff6, 0x1ba)
def s42 : Sig := (0x5ffe, 0xffffffffffffe1ff)
def s43 : Sig := (0x7bd8, 0xffffffffffffefff)
def s44 : Sig := (0x7f80, 0xe00)
def s45 : Sig := (0x7f86, 0xffffffffffffee3f)
def s46 : Sig := (0x7f98, 0xffffffffffffeecf)
def s47 : Sig := (0x7ffe, 0xffffffffffffefff)
def s48 : Sig := (0x20036, 0x8a)
def s49 : Sig := (0x2007e, 0xffffffffffffe1ff)
def s50 : Sig := (0x38000, 0x1000)
def s51 : Sig := (0x38000, 0xfffffffffffff00f)
def s52 : Sig := (0x38018, 0xfffffffffffff0cf)
def s53 : Sig := (0x3807e, 0xfffffffffffff1ff)
def s54 : Sig := (0x38f86, 0xfffffffffffff63f)
def s55 : Sig := (0x3b1fe, 0xffffffffffffffff)
def s56 : Sig := (0x3fffe, 0xffffffffffffffff)
def s57 : Sig := (0x80026, 0x0)
def s58 : Sig := (0x8007e, 0xffffffffffffe1ff)
def s59 : Sig := (0xa8006, 0xa)
def s60 : Sig := (0xa807e, 0xffffffffffffe1ff)
def s61 : Sig := (0xc8002, 0xfffffffffffff013)
def s62 : Sig := (0xc8f86, 0xfffffffffffff63f)
def s63 : Sig := (0x13007e, 0xffffffffffffe1ff)
def s64 : Sig := (0x178000, 0x1000)
def s65 : Sig := (0x178000, 0xfffffffffffff03f)
def s66 : Sig := (0x17fbd8, 0xffffffffffffffff)
def s67 : Sig := (0x17fffe, 0xffffffffffffffff)
def s68 : Sig := (0x1f8000, 0x1000)
def s69 : Sig := (0x1f8006, 0xfffffffffffff03f)
def s70 : Sig := (0x1f801e, 0xfffffffffffff0ff)
def s71 : Sig := (0x1f8026, 0x1000)
def s72 : Sig := (0x1f807e, 0xfffffffffffff1ff)
def s73 : Sig := (0x1f8186, 0xfffffffffffff63f)
def s74 : Sig := (0x1f8906, 0xfffffffffffff43f)
def s75 : Sig := (0x1f8f86, 0xfffffffffffff63f)
def s76 : Sig := (0x1ffffe, 0xffffffffffffffff)
def s77 : Sig := (0x428010, 0x8a)
def s78 : Sig := (0x42807e, 0xffffffffffffe1ff)
def s79 : Sig := (0x42ea58, 0xffffffffffffefff)
def s80 : Sig := (0x438010, 0xfffffffffffff08f)
def s81 : Sig := (0x4a8000, 0x0)
def s82 : Sig := (0x4a8036, 0x8a)
def s83 : Sig := (0x4a8036, 0xffffffffffffe0bf)
def s84 : Sig := (0x4a807e, 0xffffffffffffe1ff)
def s85 : Sig := (0x4a95b6, 0x8a)
def s86 : Sig := (0x4ab1be, 0xffffffffffffeecf)
def s87 : Sig := (0x4aea7e, 0xffffffffffffefff)
def s88 : Sig := (0x4afffe, 0xffffffffffffefff)
def s89 : Sig := (0x4b8036, 0xfffffffffffff08f)
def s90 : Sig := (0x5f8036, 0x108a)
def s91 : Sig := (0x5f8036, 0xfffffffffffff0bf)
def s92 : Sig := (0x80007e, 0xffffffffffffe1ff)
def s93 : Sig := (0x830018, 0xc)
def s94 : Sig := (0x830018, 0xffffffffffffe0cf)
def s95 : Sig := (0x83007e, 0xffffffffffffe1ff)
def s96 : Sig := (0x837ffe, 0xffffffffffffefff)
def s97 : Sig := (0x930058, 0xffffffffffffe1ff)
def s98 : Sig := (0x93005c, 0x2c)
def s99 : Sig := (0x93007e, 0xffffffffffffe1ff)
def s100 : Sig := (0x93295c, 0x42c)
def s101 : Sig := (0x9331dc, 0xffffffffffffeeef)
def s102 : Sig := (0x937ffe, 0xffffffffffffefff)
def s103 : Sig := (0x9f805e, 0xfffffffffffff03f)
def s104 : Sig := (0xa10008, 0xfffffffffffff045)
def s105 : Sig := (0xa1007e, 0xfffffffffffff1ff)
def s106 : Sig := (0xdb807e, 0xae)
def s107 : Sig := (0xdb807e, 0xffffffffffffe1ff)
def s108 : Sig := (0xe00018, 0xc0)
def s109 : Sig := (0xe38000, 0x1000)
def s110 : Sig := (0xe38010, 0x108a)
def s111 : Sig := (0xe38018, 0xfffffffffffff0cf)
def s112 : Sig := (0xe38058, 0xfffffffffffff1ff)
def s113 : Sig := (0xe3807e, 0xfffffffffffff1ff)
def s114 : Sig := (0xe3b198, 0xfffffffffffffecf)
def s115 : Sig := (0xe3fffe, 0xffffffffffffffff)
def s116 : Sig := (0xeb8036, 0x108a)
def s117 : Sig := (0xeb803e, 0xfffffffffffff0cf)
def s118 : Sig := (0xeb807e, 0xfffffffffffff1ff)
def s119 : Sig := (0xf3805c, 0xfffffffffffff0ef)
def s120 : Sig := (0xf3807e, 0xfffffffffffff1ff)
def s121 : Sig := (0xff8018, 0xfffffffffffff0cf)
def s122 : Sig := (0xff801e, 0xfffffffffffff0ff)
def s123 : Sig := (0x11c0066, 0x130)
def s124 : Sig := (0x15e8076, 0x1ba)
def s125 : Sig := (0x15e807e, 0xffffffffffffe1ff)
def s126 : Sig := (0x16c8022, 0xfffffffffffff1d3)
def s127 : Sig := (0x16cd6a2, 0xfffffffffffffbd3)
def s128 : Sig := (0x17f8026, 0xfffffffffffff1ff)
def s129 : Sig := (0x1b50048, 0xfffffffffffff175)
def s130 : Sig := (0x1b5007e, 0xfffffffffffff1ff)
def s131 : Sig := (0x1b52048, 0xffffffffffffff75)
def s132 : Sig := (0x1df807e, 0x1be)
def s133 : Sig := (0x1e00078, 0x1c0)
def s134 : Sig := (0x1e0007e, 0xffffffffffffe1ff)
def s135 : Sig := (0x1ea807e, 0x1ca)
def s136 : Sig := (0x1ef8018, 0xfffffffffffff0cf)
def s137 : Sig := (0x1f3007e, 0xffffffffffffe1ff)
def s138 : Sig := (0x1f78000, 0x1000)
def s139 : Sig := (0x1f78058, 0xfffffffffffff1ff)
def s140 : Sig := (0x1ff8000, 0x1000)
def s141 : Sig := (0x1ff8006, 0xfffffffffffff03f)
def s142 : Sig := (0x1ff8010, 0x108a)
def s143 : Sig := (0x1ff8018, 0xfffffffffffff0cf)
def s144 : Sig := (0x1ff8026, 0x1000)
def s145 : Sig := (0x1ff8036, 0x108a)
def s146 : Sig := (0x1ff8058, 0xfffffffffffff1ff)
def s147 : Sig := (0x1ff805c, 0x102c)
def s148 : Sig := (0x1ff8066, 0x1130)
def s149 : Sig := (0x1ff807e, 0x10ae)
def s150 : Sig := (0x1ff807e, 0xfffffffffffff1ff)
def s151 : Sig := (0x1ff8ffe, 0xfffffffffffff7ff)
def s152 : Sig := (0x1ff95b6, 0x108a)
def s153 : Sig := (0x1ff95fe, 0xfffffffffffff1ff)
def s154 : Sig := (0x1ffa97e, 0xfffffffffffff5ff)
def s155 : Sig := (0x1ffb1fe, 0xffffffffffffffff)
def s156 : Sig := (0x1ffff80, 0x1e00)
def s157 : Sig := (0x1fffffe, 0xffffffffffffffff)
def s158 : Sig := (0x4088482, 0x2)
def s159 : Sig := (0x40a8000, 0x0)
def s160 : Sig := (0x40a8586, 0xa)
def s161 : Sig := (0x40a8586, 0xffffffffffffe63f)
def s162 : Sig := (0x40a85fe, 0xffffffffffffe1ff)
def s163 : Sig := (0x40a8f86, 0xffffffffffffe63f)
def s164 : Sig := (0x40a95b6, 0x8a)
def s165 : Sig := (0x40afffe, 0xffffffffffffefff)
def s166 : Sig := (0x41f8586, 0xfffffffffffff03f)
def s167 : Sig := (0x41f8f86, 0xfffffffffffff63f)
def s168 : Sig := (0x4429190, 0x8a)
def s169 : Sig := (0x44291b6, 0x8a)
def s170 : Sig := (0x44295b6, 0x8a)
def s171 : Sig := (0x442b198, 0xffffffffffffeecf)
def s172 : Sig := (0x442fffe, 0xffffffffffffefff)
def s173 : Sig := (0x4439190, 0xfffffffffffff08f)
def s174 : Sig := (0x44894a2, 0x82)
def s175 : Sig := (0x44a85b6, 0x8a)
def s176 : Sig := (0x44a91b6, 0x8a)
def s177 : Sig := (0x44a95a6, 0x8a)
def s178 : Sig := (0x44ab1fe, 0xffffffffffffefff)
def s179 : Sig := (0x4e39198, 0xfffffffffffff0cf)
def s180 : Sig := (0x5ff85fe, 0xfffffffffffff1ff)
def s181 : Sig := (0x5ff9190, 0x108a)
def s182 : Sig := (0x5ff91fe, 0xfffffffffffff1ff)
def s183 : Sig := (0x8130904, 0x42c)
def s184 : Sig := (0x8130f86, 0xffffffffffffe63f)
def s185 : Sig := (0x813295c, 0x42c)
def s186 : Sig := (0x8135fa6, 0xffffffffffffefff)
def s187 : Sig := (0x8137ffe, 0xffffffffffffefff)
def s188 : Sig := (0x8138904, 0xfffffffffffff42f)
def s189 : Sig := (0x81f8106, 0xfffffffffffff43f)
def s190 : Sig := (0x81f8904, 0x142c)
def s191 : Sig := (0x81f8906, 0xfffffffffffff43f)
def s192 : Sig := (0x81f8f86, 0xfffffffffffff63f)
def s193 : Sig := (0x8832118, 0x40c)
def s194 : Sig := (0x8832118, 0xffffffffffffe4cf)
def s195 : Sig := (0x883215c, 0x42c)
def s196 : Sig := (0x883295c, 0x42c)
def s197 : Sig := (0x8833198, 0xffffffffffffeecf)
def s198 : Sig := (0x8912848, 0x424)
def s199 : Sig := (0x8912848, 0xffffffffffffef75)
def s200 : Sig := (0x8916a48, 0xffffffffffffef75)
def s201 : Sig := (0x893215c, 0x42c)
def s202 : Sig := (0x8932958, 0x42c)
def s203 : Sig := (0x89331fe, 0xffffffffffffefff)
def s204 : Sig := (0x8e3a118, 0xfffffffffffff4cf)
def s205 : Sig := (0x9ff897e, 0xfffffffffffff5ff)
def s206 : Sig := (0x9ffa17e, 0xfffffffffffff5ff)
def s207 : Sig := (0xc1b8d86, 0x42e)
def s208 : Sig := (0xc1f8d86, 0xfffffffffffff43f)
def s209 : Sig := (0xcc3b198, 0x48e)
def s210 : Sig := (0xcdbb1fe, 0xffffffffffffefff)
def s211 : Sig := (0xe038180, 0xfffffffffffff60f)
def s212 : Sig := (0xe038186, 0xfffffffffffff63f)
def s213 : Sig := (0xe038198, 0xfffffffffffff6cf)
def s214 : Sig := (0xe038f86, 0xfffffffffffff63f)
def s215 : Sig := (0xe03b198, 0xfffffffffffffecf)
def s216 : Sig := (0xe138984, 0xfffffffffffff62f)
def s217 : Sig := (0xe1f8186, 0xfffffffffffff63f)
def s218 : Sig := (0xe439190, 0xfffffffffffff68f)
def s219 : Sig := (0xfff81fe, 0xfffffffffffff7ff)
def s220 : Sig := (0x101c0e06, 0x30)
def s221 : Sig := (0x101c0f86, 0xffffffffffffe63f)
def s222 : Sig := (0x11144a40, 0x130)
def s223 : Sig := (0x11146a48, 0xffffffffffffef75)
def s224 : Sig := (0x140a8f86, 0xffffffffffffe63f)
def s225 : Sig := (0x141e8f86, 0x3a)
def s226 : Sig := (0x1556dbd0, 0x1ba)
def s227 : Sig := (0x160c8000, 0x1000)
def s228 : Sig := (0x160c8682, 0xfffffffffffff213)
def s229 : Sig := (0x160c8f86, 0xfffffffffffff63f)
def s230 : Sig := (0x19956a48, 0x534)
def s231 : Sig := (0x19956a48, 0xffffffffffffef75)
def s232 : Sig := (0x1a150000, 0x1000)
def s233 : Sig := (0x1a150a00, 0x1000)
def s234 : Sig := (0x1a150a00, 0xfffffffffffff635)
def s235 : Sig := (0x1a150f86, 0xfffffffffffff63f)
def s236 : Sig := (0x1a153bfe, 0xffffffffffffffff)
def s237 : Sig := (0x1a156a48, 0xffffffffffffff75)
def s238 : Sig := (0x1a157ffe, 0xffffffffffffffff)
def s239 : Sig := (0x1a170b04, 0xfffffffffffff63d)
def s240 : Sig := (0x1b154a40, 0x1130)
def s241 : Sig := (0x1e000f80, 0x600)
def s242 : Sig := (0x1e000f86, 0xffffffffffffe63f)
def s243 : Sig := (0x1e007f80, 0xe00)
def s244 : Sig := (0x1e080f86, 0xffffffffffffe63f)
def s245 : Sig := (0x1e178b80, 0xfffffffffffff63f)
def s246 : Sig := (0x1e1c0f86, 0xffffffffffffe63f)
def s247 : Sig := (0x1e1f8000, 0x1000)
def s248 : Sig := (0x1e1f8006, 0xfffffffffffff03f)
def s249 : Sig := (0x1e1f8586, 0x100a)
def s250 : Sig := (0x1e1f8904, 0x142c)
def s251 : Sig := (0x1e1f8906, 0xfffffffffffff43f)
def s252 : Sig := (0x1e1f8d86, 0x142e)
def s253 : Sig := (0x1e1f8e00, 0x1000)
def s254 : Sig := (0x1e1f8e06, 0x1030)
def s255 : Sig := (0x1e1f8f80, 0x1600)
def s256 : Sig := (0x1e1f8f84, 0x162c)
def s257 : Sig := (0x1e1f8f86, 0x1630)
def s258 : Sig := (0x1e1f8f86, 0xfffffffffffff63f)
def s259 : Sig := (0x1e1f8ffe, 0xfffffffffffff7ff)
def s260 : Sig := (0x1e1f95b6, 0x108a)
def s261 : Sig := (0x1e1fce66, 0x1130)
def s262 : Sig := (0x1e1fdfa6, 0xffffffffffffffff)
def s263 : Sig := (0x1e1ffffe, 0xffffffffffffffff)
def s264 : Sig := (0x1e5f8036, 0x108a)
def s265 : Sig := (0x1fff8000, 0x1000)
def s266 : Sig := (0x1fff807e, 0xfffffffffffff1ff)
def s267 : Sig := (0x1fff85b6, 0x108a)
def s268 : Sig := (0x1fff8ffe, 0xfffffffffffff7ff)
def s269 : Sig := (0x20e03018, 0x8c0)
def s270 : Sig := (0x21605020, 0x9c0)
def s271 : Sig := (0x21a06048, 0x940)
def s272 : Sig := (0x21a06a48, 0xffffffffffffef75)
def s273 : Sig := (0x24e2b198, 0x8ca)
def s274 : Sig := (0x26609080, 0xfffffffffffffac3)
def s275 : Sig := (0x26e0b098, 0xfffffffffffffac3)
def s276 : Sig := (0x276c90a2, 0xfffffffffffffbd3)
def s277 : Sig := (0x2a002000, 0xe00)
def s278 : Sig := (0x2aa10000, 0x1000)
def s279 : Sig := (0x2aa12008, 0xfffffffffffffe45)
def s280 : Sig := (0x2aa12018, 0xfffffffffffffecf)
def s281 : Sig := (0x2aa12048, 0xffffffffffffff75)
def s282 : Sig := (0x2aa13198, 0xfffffffffffffecf)
def s283 : Sig := (0x2aa16a48, 0xffffffffffffff75)
def s284 : Sig := (0x2aa32018, 0xfffffffffffffecf)
def s285 : Sig := (0x2ae3a018, 0xfffffffffffffecf)
def s286 : Sig := (0x2bb50000, 0x1000)
def s287 : Sig := (0x2bb52048, 0xffffffffffffff75)
def s288 : Sig := (0x2bffa07e, 0xffffffffffffffff)
def s289 : Sig := (0x2e003180, 0xe00)
def s290 : Sig := (0x2e003198, 0xffffffffffffeecf)
def s291 : Sig := (0x2e0031fe, 0xffffffffffffefff)
def s292 : Sig := (0x2e007f80, 0xe00)
def s293 : Sig := (0x2e03b180, 0xfffffffffffffe0f)
def s294 : Sig := (0x2e42b190, 0xe8a)
def s295 : Sig := (0x2e639180, 0xfffffffffffffecf)
def s296 : Sig := (0x2e833198, 0xe0c)
def s297 : Sig := (0x2ee38000, 0x1000)
def s298 : Sig := (0x2ee39190, 0x108a)
def s299 : Sig := (0x2ee3b018, 0x18c0)
def s300 : Sig := (0x2ee3b180, 0x1e00)
def s301 : Sig := (0x2ee3b190, 0x1e8a)
def s302 : Sig := (0x2ee3b198, 0xfffffffffffffecf)
def s303 : Sig := (0x2ee3b1fe, 0xffffffffffffffff)
def s304 : Sig := (0x2ee3fffe, 0xffffffffffffffff)
def s305 : Sig := (0x2ef3b1fe, 0xffffffffffffffff)
def s306 : Sig := (0x2f1c31e6, 0xf30)
def s307 : Sig := (0x2f1c31fe, 0xffffffffffffefff)
def s308 : Sig := (0x2f9f31fe, 0xf3c)
def s309 : Sig := (0x2fff8000, 0x1000)
def s310 : Sig := (0x2fff8066, 0x1130)
def s311 : Sig := (0x2fff807e, 0xfffffffffffff1ff)
def s312 : Sig := (0x2fff91b6, 0x108a)
def s313 : Sig := (0x2fffb198, 0xfffffffffffffecf)
def s314 : Sig := (0x2fffb1e6, 0x1f30)
def s315 : Sig := (0x2fffb1fe, 0xffffffffffffffff)
def s316 : Sig := (0x33244200, 0xfffffffffffffb51)
def s317 : Sig := (0x33645220, 0xfffffffffffffbd1)
def s318 : Sig := (0x36005680, 0xa00)
def s319 : Sig := (0x376c8000, 0x1000)
def s320 : Sig := (0x376cd020, 0x19c0)
def s321 : Sig := (0x376cd6a2, 0xfffffffffffffbd3)
def s322 : Sig := (0x376cd6a6, 0xfffffffffffffbff)
def s323 : Sig := (0x376cdfa6, 0xffffffffffffffff)
def s324 : Sig := (0x376ed7a6, 0xfffffffffffffbdb)
def s325 : Sig := (0x3a006a00, 0xe00)
def s326 : Sig := (0x3a006a48, 0xffffffffffffef75)
def s327 : Sig := (0x3b146a40, 0xf30)
def s328 : Sig := (0x3b156a40, 0xffffffffffffff35)
def s329 : Sig := (0x3bb50000, 0x1000)
def s330 : Sig := (0x3bb515b6, 0x108a)
def s331 : Sig := (0x3bb52048, 0xffffffffffffff75)
def s332 : Sig := (0x3bb54a00, 0x1000)
def s333 : Sig := (0x3bb54a40, 0x1130)
def s334 : Sig := (0x3bb56a00, 0x1e00)
def s335 : Sig := (0x3bb56a40, 0x1f30)
def s336 : Sig := (0x3bb56a48, 0xffffffffffffff75)
def s337 : Sig := (0x3bb56a58, 0xffffffffffffffff)
def s338 : Sig := (0x3bb57ffe, 0xffffffffffffffff)
def s339 : Sig := (0x3bb76a58, 0xffffffffffffffff)
def s340 : Sig := (0x3bffea7e, 0xffffffffffffffff)
def s341 : Sig := (0x3e003f80, 0xe00)
def s342 : Sig := (0x3e005f80, 0xe00)
def s343 : Sig := (0x3e007b80, 0xe00)
def s344 : Sig := (0x3eff8000, 0x1000)
def s345 : Sig := (0x3effb198, 0xfffffffffffffecf)
def s346 : Sig := (0x3effbf9e, 0xfffffffffffffeff)
def s347 : Sig := (0x3f6cdfa2, 0xffffffffffffffd3)
def s348 : Sig := (0x3f7f8000, 0x1000)
def s349 : Sig := (0x3f7f95a6, 0x108a)
def s350 : Sig := (0x3f7fdfa6, 0xffffffffffffffff)
def s351 : Sig := (0x3fefb198, 0xfffffffffffffecf)
def s352 : Sig := (0x3ff78000, 0x1000)
def s353 : Sig := (0x3ff7fbd8, 0xffffffffffffffff)
def bucketTier1 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def bucketTier2 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def bucketTier3 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def b4_12 : List (List Sig) := [
  [s40, s111, s129, s228, s279]]
def b4_29 : List (List Sig) := [
  [s3, s19, s111, s228, s336]]
def bucketTier4 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], b4_12, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], b4_29, []]

def b5_4 : List (List Sig) := [
  [s1, s33, s51, s258, s321, s336],
  [s1, s47, s51, s258, s287, s321],
  [s10, s33, s51, s111, s321, s336],
  [s17, s33, s51, s111, s321, s336],
  [s17, s47, s51, s111, s287, s321],
  [s47, s97, s139, s258, s279, s321],
  [s47, s97, s150, s258, s279, s321]]
def b5_5 : List (List Sig) := [
  [s6, s43, s69, s258, s279, s321],
  [s6, s47, s65, s258, s279, s321],
  [s6, s47, s69, s258, s279, s321],
  [s8, s43, s69, s258, s279, s321],
  [s17, s47, s65, s139, s279, s321],
  [s17, s47, s69, s139, s279, s321]]
def b5_6 : List (List Sig) := [
  [s33, s111, s161, s258, s321, s336],
  [s33, s111, s163, s258, s321, s336],
  [s33, s111, s246, s258, s321, s336],
  [s47, s111, s163, s258, s287, s321],
  [s47, s111, s224, s258, s287, s321],
  [s47, s111, s246, s258, s287, s321]]
def b5_7 : List (List Sig) := [
  [s8, s32, s111, s258, s323, s336]]
def b5_8 : List (List Sig) := [
  [s3, s19, s111, s258, s321, s336],
  [s3, s19, s150, s228, s302, s336],
  [s3, s40, s111, s228, s302, s336],
  [s8, s32, s52, s258, s321, s336],
  [s8, s32, s111, s228, s336, s350],
  [s8, s32, s111, s229, s321, s336],
  [s8, s32, s111, s237, s258, s321],
  [s8, s40, s111, s228, s302, s336],
  [s33, s94, s111, s258, s321, s336],
  [s47, s94, s111, s258, s287, s321]]
def b5_9 : List (List Sig) := [
  [s33, s55, s111, s258, s321, s336],
  [s33, s111, s236, s258, s321, s336],
  [s47, s55, s111, s258, s321, s336],
  [s47, s56, s111, s258, s287, s321],
  [s47, s66, s150, s258, s279, s321],
  [s47, s67, s139, s258, s279, s321],
  [s47, s76, s139, s258, s279, s321]]
def b5_12 : List (List Sig) := [
  [s33, s50, s111, s258, s321, s336],
  [s33, s111, s232, s258, s321, s336],
  [s33, s111, s233, s258, s321, s336],
  [s47, s50, s111, s258, s287, s321],
  [s47, s64, s139, s258, s279, s321],
  [s47, s68, s139, s258, s279, s321],
  [s47, s71, s150, s258, s279, s321]]
def b5_13 : List (List Sig) := [
  [s40, s111, s150, s227, s302, s336]]
def b5_14 : List (List Sig) := [
  [s40, s137, s150, s302, s336]]
def b5_17 : List (List Sig) := [
  [s8, s32, s80, s258, s321, s336],
  [s8, s32, s89, s258, s321, s336],
  [s8, s32, s111, s258, s321, s328]]
def b5_20 : List (List Sig) := [
  [s10, s33, s111, s234, s321, s336],
  [s17, s33, s111, s234, s321, s336]]
def b5_21 : List (List Sig) := [
  [s47, s111, s129, s258, s279, s323]]
def b5_22 : List (List Sig) := [
  [s40, s111, s129, s228, s302, s336],
  [s40, s111, s129, s258, s279, s321],
  [s47, s111, s129, s228, s279, s350],
  [s47, s111, s129, s229, s279, s321]]
def b5_24 : List (List Sig) := [
  [s40, s61, s150, s279, s302, s336]]
def b5_27 : List (List Sig) := [
  [s47, s111, s210, s258, s321, s336]]
def b5_28 : List (List Sig) := [
  [s33, s111, s199, s258, s321, s336],
  [s33, s111, s200, s258, s321, s336]]
def bucketTier5 : List (List (List Sig)) := [[], [], [], [], b5_4, b5_5, b5_6, b5_7, b5_8, b5_9, [], [], b5_12, b5_13, b5_14, [], [], b5_17, [], [], b5_20, b5_21, b5_22, [], b5_24, [], [], b5_27, b5_28, [], []]

def b6_0 : List (List Sig) := [
  [s47, s111, s129, s258, s302, s323, s336],
  [s47, s111, s247, s258, s306, s321, s336],
  [s47, s111, s258, s314, s321, s336]]
def b6_1 : List (List Sig) := [
  [s8, s32, s69, s222, s258, s321, s336],
  [s8, s32, s91, s258, s302, s321, s336],
  [s40, s111, s129, s258, s302, s321, s336],
  [s47, s111, s129, s228, s302, s336, s350],
  [s47, s111, s129, s229, s302, s321, s336],
  [s47, s111, s129, s258, s263, s279, s321],
  [s47, s111, s129, s258, s279, s321, s350]]
def b6_2 : List (List Sig) := [
  [s33, s111, s234, s258, s321, s336]]
def b6_3 : List (List Sig) := [
  [s21, s47, s99, s129, s258, s302, s321],
  [s40, s99, s150, s258, s302, s336],
  [s47, s61, s150, s279, s302, s336, s350]]
def b6_4 : List (List Sig) := [
  [s3, s40, s150, s228, s302, s336],
  [s6, s43, s150, s258, s279, s321],
  [s6, s47, s139, s258, s279, s321],
  [s6, s47, s150, s258, s279, s321],
  [s8, s33, s111, s258, s321, s336],
  [s8, s40, s150, s228, s302, s336],
  [s8, s43, s150, s258, s279, s321],
  [s8, s47, s111, s258, s281, s321],
  [s8, s47, s111, s258, s287, s321],
  [s8, s47, s139, s258, s279, s321],
  [s27, s140, s258, s302, s321, s336],
  [s47, s111, s129, s247, s258, s279, s321]]
def b6_5 : List (List Sig) := [
  [s8, s32, s258, s321, s327, s336],
  [s8, s47, s111, s197, s258, s321, s336],
  [s23, s47, s129, s258, s302, s321],
  [s47, s99, s111, s197, s258, s321, s336]]
def b6_6 : List (List Sig) := [
  [s10, s33, s111, s258, s321, s336],
  [s17, s33, s111, s258, s321, s336],
  [s17, s47, s111, s258, s287, s321],
  [s21, s47, s150, s240, s258, s302, s321],
  [s47, s150, s210, s258, s302, s321, s336]]
def b6_7 : List (List Sig) := [
  [s8, s29, s32, s111, s258, s321, s336],
  [s8, s32, s111, s183, s258, s321, s336],
  [s33, s150, s199, s258, s302, s321, s336],
  [s33, s150, s200, s258, s302, s321, s336]]
def b6_8 : List (List Sig) := [
  [s1, s33, s111, s258, s321, s336],
  [s1, s47, s111, s258, s287, s321],
  [s8, s32, s111, s258, s321, s336],
  [s8, s32, s117, s258, s321, s336],
  [s8, s34, s111, s258, s321, s336],
  [s8, s47, s90, s258, s302, s321, s336],
  [s8, s111, s171, s258, s321, s336],
  [s47, s90, s134, s258, s302, s321, s336],
  [s47, s99, s145, s258, s302, s321, s336]]
def b6_9 : List (List Sig) := [
  [s8, s32, s129, s258, s279, s321],
  [s40, s61, s150, s302, s336]]
def b6_11 : List (List Sig) := [
  [s8, s32, s111, s234, s258, s321, s336]]
def b6_12 : List (List Sig) := [
  [s8, s32, s111, s198, s258, s321, s336],
  [s33, s109, s111, s258, s321, s336],
  [s33, s111, s140, s258, s321, s336],
  [s33, s111, s247, s258, s321, s336],
  [s33, s111, s253, s258, s321, s336],
  [s33, s111, s258, s309, s321, s336],
  [s33, s111, s258, s321, s329, s336],
  [s33, s111, s258, s321, s332, s336],
  [s47, s109, s111, s258, s287, s321],
  [s47, s111, s129, s228, s258, s279, s321],
  [s47, s111, s140, s258, s287, s321],
  [s47, s111, s247, s258, s287, s321],
  [s47, s111, s258, s286, s287, s321],
  [s47, s111, s258, s287, s309, s321],
  [s47, s111, s258, s287, s321, s329],
  [s47, s111, s258, s321, s332, s336]]
def b6_13 : List (List Sig) := [
  [s47, s99, s150, s258, s302, s321, s339]]
def b6_14 : List (List Sig) := [
  [s1, s47, s51, s258, s315, s321, s336],
  [s8, s47, s69, s258, s302, s321, s337],
  [s17, s47, s51, s111, s315, s321, s336],
  [s33, s47, s51, s111, s258, s321, s336],
  [s47, s97, s139, s258, s302, s321, s336],
  [s47, s97, s150, s258, s302, s321, s336],
  [s47, s99, s139, s258, s302, s321, s336],
  [s47, s99, s150, s258, s279, s321, s353],
  [s47, s99, s150, s258, s284, s321, s336]]
def b6_15 : List (List Sig) := [
  [s6, s43, s69, s258, s302, s321, s336],
  [s6, s47, s65, s258, s302, s321, s336],
  [s6, s47, s69, s258, s302, s321, s336],
  [s8, s17, s32, s111, s258, s321, s336],
  [s8, s43, s69, s258, s302, s321, s336],
  [s8, s47, s69, s258, s279, s321, s353],
  [s8, s47, s69, s258, s280, s321, s336],
  [s17, s47, s65, s139, s302, s321, s336],
  [s17, s47, s69, s139, s302, s321, s336],
  [s17, s47, s69, s150, s279, s321, s353],
  [s33, s47, s111, s176, s258, s321],
  [s33, s47, s111, s201, s258, s336],
  [s47, s95, s129, s258, s302, s321, s336],
  [s47, s107, s129, s258, s302, s321, s336],
  [s111, s258, s287, s309, s321]]
def b6_16 : List (List Sig) := [
  [s8, s32, s93, s111, s258, s321, s336],
  [s8, s111, s258, s321, s333, s336],
  [s33, s150, s161, s258, s302, s321, s336],
  [s33, s150, s163, s258, s302, s321, s336],
  [s47, s111, s163, s258, s315, s321, s336],
  [s47, s111, s246, s258, s315, s321, s336],
  [s47, s139, s242, s258, s302, s321, s336],
  [s47, s139, s244, s258, s302, s321, s336]]
def b6_17 : List (List Sig) := [
  [s8, s32, s150, s258, s302, s323, s336],
  [s8, s47, s111, s258, s302, s323, s336],
  [s17, s47, s111, s258, s287, s321, s336],
  [s33, s51, s111, s258, s321, s336],
  [s47, s51, s111, s258, s287, s321]]
def b6_18 : List (List Sig) := [
  [s3, s19, s150, s258, s302, s321, s336],
  [s3, s40, s111, s258, s302, s321, s336],
  [s8, s32, s72, s258, s302, s321, s336],
  [s8, s32, s111, s258, s263, s321, s336],
  [s8, s32, s111, s258, s321, s336, s350],
  [s8, s32, s150, s228, s302, s336, s350],
  [s8, s32, s150, s229, s302, s321, s336],
  [s8, s32, s150, s237, s258, s302, s321],
  [s8, s40, s111, s258, s302, s321, s336],
  [s8, s47, s52, s215, s258, s321, s336],
  [s8, s47, s52, s258, s302, s321, s336],
  [s8, s47, s111, s215, s258, s321, s336],
  [s8, s47, s111, s228, s302, s336, s350],
  [s8, s47, s111, s229, s302, s321, s336],
  [s8, s47, s111, s237, s258, s302, s321],
  [s33, s111, s176, s258, s321],
  [s33, s111, s201, s258, s336],
  [s40, s47, s111, s150, s228, s302, s336],
  [s47, s63, s111, s258, s302, s321, s336],
  [s47, s65, s139, s258, s279, s321],
  [s47, s69, s139, s258, s279, s321],
  [s47, s94, s111, s258, s315, s321, s336],
  [s47, s95, s111, s258, s302, s321, s336],
  [s47, s99, s111, s258, s302, s321, s336],
  [s47, s99, s111, s258, s321, s336, s351],
  [s47, s99, s117, s258, s302, s321, s336],
  [s47, s99, s136, s258, s302, s321, s336],
  [s47, s99, s143, s258, s302, s321, s336],
  [s47, s99, s179, s258, s302, s321, s336],
  [s47, s107, s111, s258, s302, s321, s336],
  [s47, s111, s137, s258, s302, s321, s336],
  [s47, s111, s201, s258, s287]]
def b6_19 : List (List Sig) := [
  [s8, s32, s119, s258, s321, s336],
  [s33, s150, s236, s258, s302, s321, s336],
  [s33, s150, s238, s258, s302, s321, s336],
  [s47, s56, s111, s258, s315, s321, s336],
  [s47, s66, s150, s258, s302, s321, s336],
  [s47, s67, s139, s258, s302, s321, s336],
  [s47, s76, s139, s258, s302, s321, s336],
  [s47, s76, s150, s258, s279, s321, s353]]
def b6_20 : List (List Sig) := [
  [s8, s32, s69, s258, s279, s321, s336]]
def b6_21 : List (List Sig) := [
  [s8, s32, s111, s247, s258, s321, s336],
  [s29, s47, s111, s129, s258, s279, s321],
  [s40, s111, s150, s228, s302, s336],
  [s47, s111, s129, s183, s258, s279, s321]]
def b6_22 : List (List Sig) := [
  [s8, s32, s111, s254, s258, s321, s336],
  [s33, s150, s232, s258, s302, s321, s336],
  [s33, s150, s233, s258, s302, s321, s336],
  [s40, s150, s227, s302, s336],
  [s47, s50, s111, s258, s315, s321, s336],
  [s47, s64, s139, s258, s302, s321, s336],
  [s47, s68, s139, s258, s302, s321, s336],
  [s47, s68, s150, s258, s279, s321, s353],
  [s47, s69, s150, s279, s302, s323, s336],
  [s47, s71, s150, s258, s302, s321, s336],
  [s47, s90, s129, s258, s302, s321, s336],
  [s150, s186, s247, s302, s336]]
def b6_23 : List (List Sig) := [
  [s8, s32, s70, s258, s302, s321, s336],
  [s40, s69, s150, s274, s302, s336],
  [s40, s69, s150, s279, s302, s321, s336],
  [s47, s111, s150, s227, s302, s336, s350],
  [s47, s111, s150, s247, s302, s323, s336],
  [s47, s111, s247, s258, s287, s321, s336]]
def b6_24 : List (List Sig) := [
  [s8, s32, s150, s230, s258, s321, s336],
  [s40, s111, s150, s247, s302, s321, s336],
  [s47, s62, s150, s279, s302, s321, s336],
  [s47, s99, s150, s262, s302, s336],
  [s47, s137, s150, s302, s336, s350]]
def b6_25 : List (List Sig) := [
  [s17, s47, s111, s258, s306, s321, s336]]
def b6_26 : List (List Sig) := [
  [s8, s32, s51, s111, s258, s321, s336],
  [s47, s79, s150, s258, s302, s321],
  [s47, s82, s150, s231, s258, s302, s321],
  [s47, s111, s150, s258, s261, s321, s336],
  [s47, s111, s258, s308, s321, s336]]
def b6_27 : List (List Sig) := [
  [s8, s32, s69, s111, s258, s321, s336],
  [s8, s32, s98, s111, s258, s321, s336],
  [s8, s32, s111, s258, s259, s321, s336],
  [s8, s47, s80, s258, s302, s321, s336],
  [s8, s47, s89, s258, s302, s321, s336],
  [s8, s47, s111, s258, s302, s321, s328],
  [s8, s47, s173, s258, s302, s321, s336],
  [s27, s47, s111, s258, s321, s336],
  [s33, s47, s111, s217, s321, s336],
  [s33, s47, s111, s258, s287, s321],
  [s33, s47, s111, s258, s321, s336],
  [s35, s47, s111, s258, s321, s336],
  [s47, s87, s129, s258, s302, s321],
  [s47, s111, s178, s258, s321, s336],
  [s47, s111, s203, s258, s321, s336],
  [s47, s111, s258, s307, s321, s336]]
def b6_29 : List (List Sig) := [
  [s8, s32, s111, s228, s258, s321, s336],
  [s17, s39, s111, s150, s228, s302, s336],
  [s17, s47, s111, s129, s258, s279, s321]]
def b6_30 : List (List Sig) := [
  [s10, s33, s150, s234, s302, s321, s336],
  [s17, s33, s150, s234, s302, s321, s336],
  [s27, s111, s258, s321, s336],
  [s33, s47, s111, s234, s258, s321, s336],
  [s33, s111, s217, s321, s336],
  [s33, s111, s258, s287, s321],
  [s33, s111, s258, s321, s336],
  [s35, s111, s258, s321, s336],
  [s47, s111, s131, s258, s321],
  [s47, s111, s217, s276, s336],
  [s47, s111, s217, s287, s321],
  [s47, s111, s258, s287, s321],
  [s47, s111, s258, s321, s331]]
def bucketTier6 : List (List (List Sig)) := [b6_0, b6_1, b6_2, b6_3, b6_4, b6_5, b6_6, b6_7, b6_8, b6_9, [], b6_11, b6_12, b6_13, b6_14, b6_15, b6_16, b6_17, b6_18, b6_19, b6_20, b6_21, b6_22, b6_23, b6_24, b6_25, b6_26, b6_27, [], b6_29, b6_30]

def b7_0 : List (List Sig) := [
  [s8, s32, s123, s150, s258, s321, s336],
  [s8, s32, s150, s222, s258, s321, s336],
  [s8, s32, s150, s247, s258, s302, s321, s336],
  [s8, s47, s111, s222, s258, s321, s336],
  [s8, s47, s111, s247, s258, s302, s321, s336],
  [s17, s47, s111, s150, s247, s302, s321, s336],
  [s29, s47, s111, s129, s258, s302, s321, s336],
  [s40, s111, s150, s258, s302, s321, s336],
  [s47, s52, s72, s258, s302, s321, s336],
  [s47, s52, s150, s258, s302, s321, s336],
  [s47, s72, s111, s258, s302, s321, s336],
  [s47, s99, s111, s258, s302, s319, s321, s336],
  [s47, s111, s129, s183, s258, s302, s321, s336],
  [s47, s111, s150, s228, s302, s336, s350],
  [s47, s111, s150, s229, s302, s321, s336]]
def b7_1 : List (List Sig) := [
  [s8, s32, s150, s254, s258, s302, s321, s336],
  [s8, s47, s111, s255, s258, s302, s321, s336],
  [s17, s47, s134, s150, s302, s321, s336],
  [s29, s47, s111, s150, s258, s302, s319, s336],
  [s47, s68, s150, s258, s302, s321, s336, s353],
  [s47, s150, s190, s302, s321, s336],
  [s47, s150, s227, s302, s336, s350],
  [s47, s150, s247, s302, s323, s336],
  [s47, s150, s250, s302, s321, s336]]
def b7_2 : List (List Sig) := [
  [s8, s47, s85, s150, s258, s302, s321],
  [s8, s47, s100, s150, s258, s302, s336],
  [s8, s47, s150, s164, s258, s302, s321],
  [s8, s47, s150, s169, s258, s302, s321],
  [s8, s47, s150, s170, s258, s302, s321],
  [s8, s47, s150, s176, s258, s302, s321],
  [s8, s47, s150, s177, s258, s302, s321],
  [s8, s47, s150, s185, s258, s302, s336],
  [s8, s47, s150, s195, s258, s302, s336],
  [s8, s47, s150, s196, s258, s302, s336],
  [s8, s47, s150, s201, s258, s302, s336],
  [s8, s47, s150, s202, s258, s302, s336],
  [s8, s47, s150, s258, s302, s322, s336],
  [s21, s47, s84, s150, s258, s302, s321],
  [s24, s47, s82, s150, s258, s302, s321],
  [s24, s47, s150, s211, s258, s302, s321, s336],
  [s29, s47, s99, s150, s258, s302, s336],
  [s40, s150, s247, s302, s321, s336],
  [s47, s69, s150, s258, s300, s302, s321, s336],
  [s47, s69, s150, s274, s302, s336, s350],
  [s47, s69, s150, s279, s302, s321, s336, s350],
  [s47, s82, s150, s258, s302, s321, s334]]
def b7_3 : List (List Sig) := [
  [s8, s21, s47, s129, s258, s302, s321],
  [s8, s47, s150, s194, s258, s302, s321, s336],
  [s8, s111, s258, s297, s302, s321, s336],
  [s8, s111, s258, s302, s321, s329, s336],
  [s17, s47, s139, s150, s258, s302, s321, s336],
  [s47, s69, s150, s275, s302, s321, s336],
  [s47, s76, s150, s258, s279, s302, s321, s336],
  [s47, s90, s150, s247, s258, s302, s321, s336],
  [s47, s111, s150, s247, s302, s321, s336, s350],
  [s47, s145, s150, s247, s258, s302, s321, s336]]
def b7_4 : List (List Sig) := [
  [s8, s44, s140, s258, s302, s321, s336],
  [s8, s47, s150, s258, s301, s321, s336],
  [s8, s258, s289, s297, s302, s321, s336],
  [s8, s258, s289, s302, s321, s329, s336]]
def b7_5 : List (List Sig) := [
  [s1, s47, s51, s150, s258, s302, s321, s336],
  [s8, s32, s47, s111, s258, s321, s336],
  [s8, s32, s150, s220, s258, s321, s336],
  [s8, s47, s51, s111, s258, s302, s321, s336],
  [s17, s47, s51, s111, s150, s302, s321, s336],
  [s47, s99, s111, s150, s258, s302, s321, s336]]
def b7_6 : List (List Sig) := [
  [s8, s32, s69, s150, s258, s302, s321, s336],
  [s8, s32, s98, s150, s258, s302, s321, s336],
  [s8, s32, s150, s258, s259, s302, s321, s336],
  [s8, s47, s69, s111, s258, s302, s321, s336],
  [s8, s47, s98, s111, s258, s302, s321, s336],
  [s8, s47, s111, s193, s258, s302, s321, s336],
  [s8, s47, s111, s211, s258, s302, s321, s336],
  [s8, s47, s111, s258, s259, s302, s321, s336],
  [s8, s47, s150, s209, s258, s302, s321, s336],
  [s8, s47, s150, s213, s258, s302, s321, s336],
  [s8, s47, s150, s250, s302, s321, s336],
  [s8, s47, s191, s302, s321, s336],
  [s17, s47, s69, s111, s150, s302, s321, s336],
  [s17, s47, s111, s150, s258, s302, s323, s336],
  [s21, s47, s150, s239, s302, s321],
  [s21, s47, s150, s258, s302, s321, s333],
  [s27, s47, s150, s258, s302, s321, s336],
  [s33, s47, s111, s258, s315, s321, s336],
  [s33, s47, s150, s217, s302, s321, s336],
  [s33, s47, s150, s258, s287, s302, s321],
  [s33, s47, s150, s258, s302, s321, s336],
  [s35, s47, s150, s258, s302, s321, s336],
  [s47, s68, s150, s258, s279, s302, s321, s336],
  [s47, s87, s150, s258, s302, s321, s336],
  [s47, s150, s178, s258, s302, s321, s336],
  [s47, s150, s203, s258, s302, s321, s336],
  [s140, s150, s258, s298, s302, s321, s336]]
def b7_7 : List (List Sig) := [
  [s8, s47, s211, s258, s289, s302, s321, s336],
  [s8, s47, s211, s258, s302, s321, s325, s336],
  [s17, s39, s150, s228, s302, s336],
  [s17, s47, s111, s150, s258, s302, s321, s336],
  [s17, s47, s117, s150, s258, s302, s321, s336],
  [s17, s47, s143, s150, s258, s302, s321, s336],
  [s31, s47, s111, s150, s258, s302, s321, s336],
  [s47, s69, s150, s302, s323, s336],
  [s47, s111, s150, s163, s258, s302, s321, s336],
  [s47, s111, s150, s184, s258, s302, s321, s336],
  [s47, s111, s150, s221, s258, s302, s321, s336],
  [s47, s111, s150, s246, s258, s302, s321, s336]]
def b7_8 : List (List Sig) := [
  [s8, s32, s111, s258, s321, s336],
  [s8, s32, s150, s228, s258, s302, s321, s336],
  [s8, s47, s111, s228, s258, s302, s321, s336],
  [s8, s47, s145, s258, s302, s321, s336],
  [s17, s39, s111, s150, s258, s302, s321, s336],
  [s17, s47, s111, s129, s258, s302, s321, s336],
  [s17, s47, s111, s150, s228, s302, s321, s336],
  [s17, s47, s111, s150, s270, s302, s321, s336],
  [s40, s69, s150, s302, s321, s336],
  [s47, s69, s150, s295, s321, s336],
  [s47, s150, s258, s302, s321, s337]]
def b7_9 : List (List Sig) := [
  [s8, s32, s148, s258, s302, s321, s336],
  [s8, s47, s111, s258, s300, s321, s336],
  [s8, s47, s150, s258, s302, s324, s336],
  [s21, s47, s150, s258, s302, s321, s330],
  [s27, s150, s258, s302, s321, s336],
  [s33, s47, s150, s234, s258, s302, s321, s336],
  [s33, s111, s258, s315, s321, s336],
  [s33, s150, s217, s302, s321, s336],
  [s33, s150, s258, s287, s302, s321],
  [s33, s150, s258, s302, s321, s336],
  [s35, s150, s258, s302, s321, s336],
  [s47, s53, s258, s302, s321, s336],
  [s47, s54, s150, s302, s321, s336],
  [s47, s62, s150, s302, s321, s336],
  [s47, s69, s150, s218, s302, s321, s336],
  [s47, s73, s150, s302, s321, s336],
  [s47, s75, s114, s150, s321, s336],
  [s47, s75, s127, s150, s302, s336],
  [s47, s75, s150, s302, s321, s336],
  [s47, s80, s150, s258, s302, s321, s336],
  [s47, s82, s150, s197, s258, s302, s321, s336],
  [s47, s82, s150, s258, s298, s302, s321],
  [s47, s89, s150, s258, s302, s321, s336],
  [s47, s94, s111, s150, s258, s302, s321, s336],
  [s47, s105, s258, s302, s321, s336],
  [s47, s111, s150, s258, s302, s321, s328],
  [s47, s111, s155, s258, s321, s336],
  [s47, s111, s217, s315, s321, s336],
  [s47, s111, s258, s287, s315, s321],
  [s47, s111, s258, s288, s321, s336],
  [s47, s111, s258, s315, s321, s336],
  [s47, s112, s258, s302, s321, s336],
  [s47, s113, s258, s283, s302, s321],
  [s47, s113, s258, s302, s321, s336],
  [s47, s118, s258, s302, s321, s336],
  [s47, s120, s258, s302, s321, s336],
  [s47, s139, s150, s247, s258, s302, s321, s336],
  [s47, s139, s245, s302, s321, s336],
  [s47, s139, s258, s302, s321, s336],
  [s47, s146, s258, s302, s321, s336],
  [s47, s150, s167, s302, s321, s336],
  [s47, s150, s192, s302, s321, s336],
  [s47, s150, s217, s276, s302, s336]]
def b7_10 : List (List Sig) := [
  [s47, s56, s111, s150, s258, s302, s321, s336],
  [s47, s86, s150, s258, s302, s321, s336],
  [s47, s111, s258, s287, s321, s336],
  [s47, s150, s258, s302, s321, s330]]
def b7_11 : List (List Sig) := [
  [s47, s91, s129, s258, s302, s321, s336],
  [s47, s111, s129, s258, s263, s302, s321, s336],
  [s47, s111, s129, s258, s302, s321, s336, s350]]
def b7_12 : List (List Sig) := [
  [s17, s47, s135, s150, s302, s321, s336],
  [s33, s150, s234, s258, s302, s321, s336]]
def b7_13 : List (List Sig) := [
  [s8, s32, s140, s258, s302, s321, s336],
  [s8, s47, s150, s258, s302, s321, s337],
  [s8, s47, s150, s258, s302, s323, s336],
  [s21, s47, s99, s150, s258, s302, s321, s336],
  [s47, s48, s99, s150, s258, s302, s321, s336],
  [s47, s50, s111, s150, s258, s302, s321, s336],
  [s47, s68, s111, s150, s258, s302, s321, s336],
  [s47, s69, s302, s321, s336, s342],
  [s47, s82, s99, s150, s258, s302, s321, s336],
  [s47, s99, s150, s258, s302, s336, s350],
  [s47, s111, s150, s227, s258, s302, s321, s336],
  [s47, s111, s150, s247, s258, s302, s321, s336],
  [s47, s111, s150, s247, s258, s321, s336, s345],
  [s47, s117, s150, s247, s258, s302, s321, s336],
  [s47, s121, s150, s247, s258, s302, s321, s336],
  [s47, s143, s150, s247, s258, s302, s321, s336]]
def b7_14 : List (List Sig) := [
  [s3, s40, s150, s258, s302, s321, s336],
  [s3, s47, s128, s258, s302, s321, s336],
  [s3, s47, s150, s258, s302, s321, s336],
  [s4, s8, s47, s69, s258, s302, s321, s336],
  [s6, s43, s150, s258, s302, s321, s336],
  [s6, s47, s139, s258, s302, s321, s336],
  [s6, s47, s150, s258, s302, s321, s336],
  [s8, s33, s150, s258, s302, s321, s336],
  [s8, s40, s150, s258, s302, s321, s336],
  [s8, s43, s150, s258, s302, s321, s336],
  [s8, s47, s69, s82, s258, s302, s321, s336],
  [s8, s47, s69, s168, s258, s302, s321, s336],
  [s8, s47, s72, s258, s302, s321, s336],
  [s8, s47, s75, s150, s302, s321, s336],
  [s8, s47, s111, s258, s303, s321, s336],
  [s8, s47, s111, s258, s315, s321, s336],
  [s8, s47, s113, s258, s302, s321, s336],
  [s8, s47, s114, s150, s258, s321, s336],
  [s8, s47, s128, s258, s302, s321, s336],
  [s8, s47, s139, s258, s302, s321, s336],
  [s8, s47, s150, s212, s302, s321, s336],
  [s8, s47, s150, s214, s302, s321, s336],
  [s8, s47, s150, s215, s258, s321, s336],
  [s8, s47, s150, s217, s302, s321, s336],
  [s8, s47, s150, s228, s302, s336, s350],
  [s8, s47, s150, s229, s302, s321, s336],
  [s8, s47, s150, s245, s302, s321, s336],
  [s8, s47, s150, s258, s279, s321, s353],
  [s8, s47, s150, s258, s280, s321, s336],
  [s8, s47, s150, s258, s282, s321, s336],
  [s8, s47, s150, s258, s285, s321, s336],
  [s8, s47, s150, s258, s295, s321, s336],
  [s8, s47, s150, s258, s302, s321, s336],
  [s8, s47, s153, s258, s302, s321, s336],
  [s8, s47, s180, s258, s302, s321, s336],
  [s8, s47, s182, s258, s302, s321, s336],
  [s8, s88, s150, s258, s302, s321, s336],
  [s8, s102, s150, s258, s302, s321, s336],
  [s8, s150, s165, s258, s302, s321, s336],
  [s8, s150, s172, s258, s302, s321, s336],
  [s9, s47, s150, s258, s302, s321, s336],
  [s13, s47, s150, s258, s302, s321, s336],
  [s15, s47, s150, s258, s302, s321, s336],
  [s17, s47, s69, s82, s150, s302, s321, s336],
  [s17, s47, s69, s150, s168, s302, s321, s336],
  [s20, s47, s150, s258, s302, s321, s336],
  [s24, s47, s150, s258, s302, s321, s336],
  [s26, s47, s150, s258, s302, s321, s336],
  [s33, s47, s111, s150, s258, s321, s336],
  [s42, s47, s150, s258, s302, s321, s336],
  [s47, s49, s150, s258, s302, s321, s336],
  [s47, s58, s150, s258, s302, s321, s336],
  [s47, s60, s150, s258, s302, s321, s336],
  [s47, s63, s150, s258, s302, s321, s336],
  [s47, s78, s150, s258, s302, s321, s336],
  [s47, s84, s150, s258, s302, s321, s336],
  [s47, s92, s150, s258, s302, s321, s336],
  [s47, s95, s150, s258, s302, s321, s336],
  [s47, s99, s150, s258, s302, s321, s336],
  [s47, s107, s150, s258, s302, s321, s336],
  [s47, s111, s129, s247, s258, s302, s321, s336],
  [s47, s111, s150, s254, s258, s302, s321, s336],
  [s47, s125, s150, s258, s302, s321, s336],
  [s47, s137, s150, s258, s302, s321, s336],
  [s47, s140, s258, s288, s302, s321, s336],
  [s47, s149, s150, s258, s302, s321, s336],
  [s47, s150, s156, s258, s302, s321, s336],
  [s47, s150, s162, s258, s302, s321, s336]]
def b7_15 : List (List Sig) := [
  [s8, s45, s150, s258, s302, s321, s336],
  [s8, s47, s150, s197, s258, s302, s321, s336],
  [s8, s47, s150, s218, s258, s302, s321, s336],
  [s11, s47, s150, s258, s302, s321, s336],
  [s47, s82, s150, s221, s258, s302, s321, s336],
  [s47, s82, s150, s242, s258, s302, s321, s336],
  [s47, s84, s129, s258, s302, s321, s336],
  [s47, s99, s150, s197, s258, s302, s321, s336],
  [s47, s111, s150, s257, s258, s302, s321, s336]]
def b7_16 : List (List Sig) := [
  [s10, s33, s150, s258, s302, s321, s336],
  [s17, s33, s150, s258, s302, s321, s336],
  [s17, s47, s111, s258, s315, s321, s336],
  [s17, s47, s139, s258, s302, s321, s336],
  [s47, s69, s150, s299, s302, s321, s336]]
def b7_17 : List (List Sig) := [
  [s8, s29, s32, s150, s258, s302, s321, s336],
  [s8, s29, s47, s111, s258, s302, s321, s336],
  [s8, s32, s150, s183, s258, s302, s321, s336],
  [s8, s47, s111, s183, s258, s302, s321, s336],
  [s8, s114, s150, s258, s321, s336],
  [s17, s47, s111, s133, s150, s302, s321, s336],
  [s24, s47, s150, s234, s258, s302, s321, s336],
  [s33, s111, s150, s258, s321, s336],
  [s47, s111, s150, s258, s287, s321],
  [s47, s132, s150, s258, s302, s321, s336],
  [s150, s156, s258, s302, s321, s336],
  [s150, s247, s302, s319, s336, s350]]
def b7_18 : List (List Sig) := [
  [s1, s47, s111, s258, s315, s321, s336],
  [s8, s32, s150, s258, s302, s321, s336],
  [s8, s34, s150, s258, s302, s321, s336],
  [s8, s46, s150, s258, s302, s321, s336],
  [s8, s47, s111, s258, s302, s321, s336],
  [s8, s47, s117, s258, s302, s321, s336],
  [s8, s47, s143, s258, s302, s321, s336],
  [s8, s47, s179, s258, s302, s321, s336],
  [s8, s47, s258, s294, s302, s321, s336],
  [s8, s150, s171, s258, s302, s321, s336],
  [s24, s47, s111, s258, s302, s321, s336],
  [s47, s76, s150, s168, s258, s302, s321, s336],
  [s47, s84, s111, s258, s302, s321, s336],
  [s47, s99, s111, s258, s302, s321, s336],
  [s47, s111, s258, s306, s321, s336],
  [s47, s150, s258, s302, s310, s321, s336]]
def b7_19 : List (List Sig) := [
  [s2, s47, s150, s258, s302, s321, s336],
  [s8, s32, s69, s258, s302, s321, s336],
  [s8, s32, s129, s258, s302, s321, s336],
  [s8, s38, s150, s258, s302, s321, s336],
  [s8, s47, s111, s258, s279, s321, s336],
  [s8, s47, s122, s258, s302, s321, s336],
  [s8, s47, s243, s258, s302, s321, s336],
  [s8, s47, s258, s277, s302, s321, s336],
  [s8, s47, s258, s289, s302, s321, s336],
  [s8, s47, s258, s292, s302, s321, s336],
  [s8, s47, s258, s302, s321, s336, s341],
  [s8, s47, s258, s302, s321, s336, s342],
  [s8, s47, s258, s302, s321, s336, s343],
  [s13, s47, s258, s302, s321, s336, s343],
  [s17, s47, s82, s150, s258, s279, s302, s321],
  [s24, s47, s258, s289, s302, s321, s336],
  [s26, s47, s258, s302, s321, s336, s342],
  [s33, s47, s123, s150, s258, s321, s336],
  [s47, s61, s150, s302, s336, s350],
  [s47, s69, s150, s302, s336, s347],
  [s47, s74, s150, s302, s321, s336],
  [s47, s90, s150, s258, s272, s302, s321, s336],
  [s47, s150, s189, s302, s321, s336],
  [s47, s150, s191, s302, s321, s336],
  [s47, s150, s208, s302, s321, s336],
  [s47, s150, s251, s302, s321, s336]]
def b7_20 : List (List Sig) := [
  [s8, s47, s69, s258, s300, s302, s321, s336],
  [s47, s69, s150, s273, s302, s321, s336],
  [s47, s150, s226, s258, s321, s353]]
def b7_21 : List (List Sig) := [
  [s8, s32, s150, s234, s258, s302, s321, s336],
  [s8, s47, s69, s269, s302, s321, s336],
  [s8, s47, s111, s234, s258, s302, s321, s336],
  [s47, s68, s82, s150, s258, s302, s321, s336],
  [s47, s68, s150, s168, s258, s302, s321, s336],
  [s47, s90, s150, s258, s302, s321, s336],
  [s47, s101, s150, s258, s302, s321, s336],
  [s47, s102, s150, s258, s279, s302, s321, s336],
  [s47, s110, s150, s258, s302, s321, s336],
  [s47, s111, s150, s207, s258, s302, s321, s336],
  [s47, s111, s150, s258, s302, s321, s335],
  [s47, s116, s150, s258, s302, s321, s336],
  [s47, s142, s150, s258, s302, s321, s336],
  [s47, s145, s150, s258, s302, s321, s336],
  [s47, s150, s152, s258, s302, s321, s336],
  [s47, s150, s181, s258, s302, s321, s336],
  [s47, s150, s258, s260, s302, s321, s336],
  [s47, s150, s258, s264, s302, s321, s336],
  [s47, s150, s258, s267, s302, s321, s336],
  [s47, s150, s258, s302, s312, s321, s336],
  [s47, s150, s258, s302, s321, s336, s349]]
def b7_22 : List (List Sig) := [
  [s8, s32, s150, s198, s258, s302, s321, s336],
  [s8, s47, s111, s198, s258, s302, s321, s336],
  [s17, s47, s108, s111, s150, s302, s321, s336],
  [s17, s150, s270, s302, s319, s336],
  [s24, s47, s129, s150, s258, s302, s321],
  [s33, s123, s150, s258, s321, s336],
  [s33, s140, s150, s258, s302, s321, s336],
  [s33, s150, s247, s258, s302, s321, s336],
  [s33, s150, s253, s258, s302, s321, s336],
  [s33, s150, s258, s302, s309, s321, s336],
  [s33, s150, s258, s302, s321, s329, s336],
  [s33, s150, s258, s302, s321, s332, s336],
  [s47, s69, s150, s183, s279, s302, s321, s336],
  [s47, s109, s111, s258, s315, s321, s336],
  [s47, s111, s129, s228, s258, s302, s321, s336],
  [s47, s111, s129, s258, s279, s321],
  [s47, s111, s140, s258, s315, s321, s336],
  [s47, s111, s148, s258, s302, s321, s336],
  [s47, s111, s247, s258, s315, s321, s336],
  [s47, s111, s258, s309, s315, s321, s336],
  [s47, s111, s258, s315, s321, s329, s336],
  [s47, s138, s139, s258, s302, s321, s336],
  [s47, s139, s140, s258, s302, s321, s336],
  [s47, s139, s247, s258, s302, s321, s336],
  [s47, s139, s258, s297, s302, s321, s336],
  [s47, s139, s258, s302, s321, s336, s352],
  [s47, s144, s150, s258, s302, s321, s336]]
def b7_23 : List (List Sig) := [
  [s17, s21, s47, s129, s150, s258, s302, s321],
  [s17, s111, s150, s258, s302, s319, s321, s336],
  [s47, s94, s99, s150, s258, s302, s321, s336],
  [s47, s111, s150, s183, s247, s302, s321, s336],
  [s47, s150, s252, s302, s321, s336]]
def b7_24 : List (List Sig) := [
  [s1, s8, s47, s69, s258, s302, s321, s336],
  [s8, s47, s150, s191, s302, s321, s336],
  [s8, s47, s150, s216, s302, s321, s336],
  [s8, s47, s150, s258, s293, s302, s321, s336],
  [s8, s47, s258, s291, s302, s321, s336],
  [s47, s61, s150, s258, s279, s302, s321, s336],
  [s47, s69, s126, s258, s279, s302, s321, s336],
  [s47, s72, s258, s279, s302, s321, s336],
  [s47, s99, s150, s258, s270, s302, s336],
  [s47, s99, s150, s258, s302, s305, s321, s336],
  [s47, s99, s150, s258, s302, s321, s336, s353],
  [s47, s150, s226, s258, s302, s321]]
def b7_25 : List (List Sig) := [
  [s8, s17, s32, s150, s258, s302, s321, s336],
  [s8, s17, s47, s111, s258, s302, s321, s336],
  [s8, s47, s69, s258, s302, s303, s321, s336],
  [s8, s47, s69, s258, s302, s321, s336, s353],
  [s8, s47, s150, s258, s302, s336, s347],
  [s8, s47, s206, s258, s302, s321, s336],
  [s17, s47, s69, s150, s302, s321, s336, s353],
  [s28, s47, s150, s258, s302, s321, s336],
  [s33, s47, s150, s176, s258, s302, s321],
  [s33, s47, s150, s201, s258, s302, s336],
  [s47, s82, s87, s150, s258, s302, s321],
  [s47, s82, s150, s247, s258, s279, s302, s321],
  [s111, s258, s309, s315, s321, s336],
  [s113, s258, s297, s302, s321, s336],
  [s139, s258, s302, s321, s336, s352]]
def b7_26 : List (List Sig) := [
  [s8, s32, s111, s150, s258, s321, s336],
  [s8, s47, s93, s111, s258, s302, s321, s336],
  [s17, s47, s111, s150, s271, s302, s321, s336],
  [s29, s47, s111, s150, s258, s302, s316, s336],
  [s47, s82, s150, s200, s258, s302, s321],
  [s47, s82, s150, s223, s258, s302, s321],
  [s47, s82, s150, s258, s302, s321, s326],
  [s47, s111, s150, s258, s321, s333, s336],
  [s47, s150, s163, s258, s302, s315, s321, s336],
  [s47, s150, s186, s258, s302, s336]]
def b7_27 : List (List Sig) := [
  [s8, s47, s75, s302, s321, s336],
  [s8, s47, s111, s258, s289, s321, s336],
  [s8, s47, s114, s258, s321, s336],
  [s8, s47, s150, s256, s302, s321, s336],
  [s8, s47, s258, s296, s302, s321, s336],
  [s33, s47, s111, s258, s321, s336],
  [s40, s47, s150, s228, s302, s336],
  [s47, s51, s111, s258, s315, s321, s336],
  [s47, s53, s150, s258, s302, s321, s336]]
def b7_28 : List (List Sig) := [
  [s5, s47, s150, s258, s302, s321, s336],
  [s8, s32, s150, s258, s263, s302, s321, s336],
  [s8, s32, s150, s258, s302, s321, s336, s350],
  [s8, s47, s91, s258, s302, s321, s336],
  [s8, s47, s111, s258, s263, s302, s321, s336],
  [s8, s47, s111, s258, s302, s321, s336, s350],
  [s8, s47, s150, s215, s258, s302, s321, s336],
  [s8, s47, s258, s290, s302, s321, s336],
  [s17, s47, s91, s150, s302, s321, s336],
  [s17, s47, s145, s150, s258, s302, s321, s336],
  [s21, s47, s130, s258, s302, s321],
  [s21, s47, s150, s235, s302, s321],
  [s22, s47, s150, s258, s302, s321, s336],
  [s25, s47, s69, s150, s302, s321, s336],
  [s33, s150, s176, s258, s302, s321],
  [s33, s150, s201, s258, s302, s336],
  [s40, s47, s111, s150, s258, s302, s321, s336],
  [s47, s65, s139, s258, s302, s321, s336],
  [s47, s69, s139, s258, s302, s321, s336],
  [s47, s69, s150, s258, s279, s321, s353],
  [s47, s75, s85, s150, s302, s321],
  [s47, s75, s100, s150, s302, s336],
  [s47, s82, s150, s258, s285, s321],
  [s47, s83, s150, s258, s302, s321, s336],
  [s47, s85, s114, s150, s258, s321],
  [s47, s96, s111, s150, s258, s302, s321, s336],
  [s47, s99, s150, s258, s302, s321, s336, s351],
  [s47, s100, s114, s150, s258, s336],
  [s47, s102, s111, s150, s258, s302, s321, s336],
  [s47, s111, s150, s187, s258, s302, s321, s336],
  [s47, s111, s176, s258, s315, s321],
  [s47, s111, s201, s258, s315, s336],
  [s47, s139, s202, s258, s302, s336]]
def b7_29 : List (List Sig) := [
  [s8, s36, s150, s258, s302, s321, s336],
  [s8, s47, s119, s258, s302, s321, s336],
  [s8, s47, s150, s193, s258, s302, s316, s336],
  [s8, s47, s204, s258, s302, s321, s336],
  [s8, s150, s258, s298, s302, s321, s336],
  [s21, s47, s129, s150, s247, s258, s302, s321],
  [s47, s76, s150, s258, s302, s321, s336, s353],
  [s47, s99, s150, s258, s279, s302, s321, s336],
  [s47, s150, s188, s302, s321, s336],
  [s111, s150, s247, s258, s302, s319, s321, s336]]
def b7_30 : List (List Sig) := [
  [s8, s47, s69, s258, s279, s302, s321, s336],
  [s8, s150, s258, s278, s302, s321, s336],
  [s8, s150, s258, s297, s302, s321, s336],
  [s8, s150, s258, s302, s309, s321, s336],
  [s8, s150, s258, s302, s321, s336, s344],
  [s8, s150, s258, s302, s321, s336, s348],
  [s8, s150, s258, s302, s321, s336, s352],
  [s12, s47, s150, s258, s279, s321],
  [s17, s47, s69, s150, s279, s302, s321, s336],
  [s17, s47, s111, s150, s258, s302, s320, s336],
  [s24, s150, s258, s297, s302, s321, s336],
  [s24, s150, s258, s302, s321, s329, s336],
  [s33, s111, s258, s321, s336],
  [s40, s150, s228, s302, s336],
  [s47, s57, s150, s258, s279, s321],
  [s47, s111, s150, s258, s302, s323, s336],
  [s47, s111, s258, s287, s321],
  [s58, s150, s258, s302, s321, s336, s352],
  [s84, s150, s258, s297, s302, s321, s336],
  [s92, s150, s258, s302, s321, s336, s348],
  [s140, s150, s156, s258, s302, s321, s336]]
def bucketTier7 : List (List (List Sig)) := [b7_0, b7_1, b7_2, b7_3, b7_4, b7_5, b7_6, b7_7, b7_8, b7_9, b7_10, b7_11, b7_12, b7_13, b7_14, b7_15, b7_16, b7_17, b7_18, b7_19, b7_20, b7_21, b7_22, b7_23, b7_24, b7_25, b7_26, b7_27, b7_28, b7_29, b7_30]

def b8_0 : List (List Sig) := [
  [s8, s47, s150, s160, s258, s302, s321, s336],
  [s21, s47, s150, s234, s258, s302, s321],
  [s47, s111, s150, s258, s302, s321, s336],
  [s47, s117, s150, s258, s302, s321, s336],
  [s47, s143, s150, s258, s302, s321, s336],
  [s47, s150, s158, s258, s302, s321, s336]]
def b8_1 : List (List Sig) := [
  [s17, s150, s258, s302, s319, s321, s336],
  [s47, s69, s150, s174, s258, s302, s321, s336],
  [s47, s104, s150, s258, s302, s321, s336],
  [s47, s106, s150, s258, s302, s321, s336],
  [s47, s111, s129, s258, s302, s321, s336],
  [s47, s122, s150, s258, s302, s321, s336],
  [s47, s140, s150, s258, s302, s315, s321, s336],
  [s47, s140, s150, s258, s302, s321, s336, s353],
  [s47, s150, s183, s247, s302, s321, s336],
  [s47, s150, s247, s258, s302, s315, s321, s336],
  [s47, s150, s250, s302, s321, s336],
  [s47, s150, s258, s302, s309, s315, s321, s336]]
def b8_2 : List (List Sig) := [
  [s7, s8, s47, s150, s258, s302, s321, s336],
  [s8, s47, s69, s150, s258, s302, s321, s336],
  [s8, s47, s98, s150, s258, s302, s321, s336],
  [s8, s47, s150, s193, s258, s302, s321, s336],
  [s8, s47, s150, s211, s258, s302, s321, s336],
  [s8, s47, s150, s258, s259, s302, s321, s336],
  [s8, s47, s150, s258, s268, s302, s321, s336]]
def b8_3 : List (List Sig) := [
  [s47, s69, s150, s269, s302, s321, s336]]
def b8_4 : List (List Sig) := [
  [s8, s47, s150, s228, s258, s302, s321, s336],
  [s41, s47, s150, s258, s302, s321, s336],
  [s47, s124, s150, s258, s302, s321, s336],
  [s47, s150, s160, s258, s302, s317, s336],
  [s47, s150, s258, s302, s324, s336],
  [s140, s150, s157, s258, s302, s321, s336],
  [s150, s258, s302, s309, s315, s321, s336]]
def b8_5 : List (List Sig) := [
  [s8, s47, s111, s150, s258, s302, s321, s336],
  [s47, s82, s88, s150, s258, s302, s321, s336],
  [s47, s140, s150, s258, s302, s313, s321, s336]]
def b8_6 : List (List Sig) := [
  [s8, s44, s47, s150, s258, s302, s321, s336],
  [s8, s47, s150, s258, s289, s302, s321, s336],
  [s8, s47, s157, s258, s302, s321, s336],
  [s24, s47, s150, s258, s302, s321, s325, s336],
  [s33, s47, s150, s258, s302, s321, s336],
  [s40, s47, s150, s258, s302, s321, s336],
  [s47, s88, s150, s258, s302, s321, s336],
  [s47, s102, s150, s258, s302, s321, s336],
  [s47, s150, s165, s258, s302, s321, s336],
  [s47, s150, s187, s258, s302, s321, s336]]
def b8_7 : List (List Sig) := [
  [s17, s47, s111, s150, s258, s302, s321, s336],
  [s21, s47, s150, s258, s302, s321, s338],
  [s47, s69, s150, s183, s302, s321, s336],
  [s47, s69, s150, s258, s302, s321, s336, s353],
  [s47, s82, s150, s258, s302, s321, s340],
  [s47, s85, s150, s157, s258, s302, s321],
  [s47, s100, s150, s157, s258, s302, s336],
  [s47, s150, s154, s258, s302, s321, s336],
  [s47, s150, s176, s258, s302, s315, s321],
  [s47, s150, s201, s258, s302, s315, s336],
  [s47, s150, s205, s258, s302, s321, s336],
  [s47, s150, s206, s258, s302, s321, s336],
  [s140, s150, s258, s297, s302, s321, s336],
  [s150, s247, s258, s302, s319, s321, s336]]
def b8_8 : List (List Sig) := [
  [s4, s47, s150, s258, s302, s321, s336],
  [s17, s47, s150, s258, s302, s320, s336],
  [s21, s47, s150, s258, s302, s321, s336],
  [s47, s77, s150, s258, s302, s321, s336],
  [s47, s82, s150, s258, s302, s321, s336],
  [s47, s85, s150, s258, s302, s321, s336],
  [s47, s93, s111, s150, s258, s302, s321, s336],
  [s47, s150, s164, s258, s302, s321, s336],
  [s47, s150, s175, s258, s302, s321, s336],
  [s47, s150, s176, s258, s302, s321, s336],
  [s47, s150, s177, s258, s302, s321, s336],
  [s47, s150, s191, s258, s302, s321, s336],
  [s47, s150, s249, s258, s302, s321, s336],
  [s47, s150, s258, s302, s323, s336]]
def b8_9 : List (List Sig) := [
  [s1, s47, s111, s150, s258, s302, s321, s336],
  [s8, s44, s150, s258, s302, s321, s336],
  [s8, s47, s140, s258, s302, s321, s336],
  [s12, s47, s150, s258, s302, s321, s336],
  [s17, s47, s150, s247, s302, s321, s336],
  [s33, s150, s258, s302, s321, s336],
  [s40, s150, s258, s302, s321, s336],
  [s47, s57, s150, s258, s302, s321, s336],
  [s47, s61, s150, s258, s302, s321, s336],
  [s47, s69, s126, s258, s302, s321, s336],
  [s47, s69, s150, s241, s302, s321, s336],
  [s47, s72, s258, s302, s321, s336],
  [s47, s75, s150, s302, s321, s336],
  [s47, s81, s150, s258, s302, s321, s336],
  [s47, s82, s129, s258, s302, s321, s336],
  [s47, s111, s258, s315, s321, s336],
  [s47, s113, s258, s302, s321, s336],
  [s47, s128, s258, s302, s321, s336],
  [s47, s139, s258, s302, s321, s336],
  [s47, s150, s159, s258, s302, s321, s336],
  [s47, s150, s217, s302, s321, s336],
  [s47, s150, s228, s302, s336, s350],
  [s47, s150, s229, s302, s321, s336],
  [s47, s150, s247, s258, s266, s302, s321, s336]]
def b8_10 : List (List Sig) := [
  [s21, s47, s150, s258, s302, s321, s329],
  [s29, s47, s150, s258, s302, s319, s336],
  [s47, s91, s150, s258, s302, s321, s336],
  [s47, s111, s150, s258, s263, s302, s321, s336],
  [s47, s111, s150, s258, s302, s321, s336, s350],
  [s47, s147, s150, s258, s302, s321, s336]]
def b8_11 : List (List Sig) := [
  [s47, s119, s150, s258, s302, s321, s336]]
def b8_12 : List (List Sig) := [
  [s37, s47, s150, s258, s302, s321, s336],
  [s47, s69, s150, s258, s279, s302, s321, s336],
  [s47, s82, s150, s258, s279, s302, s321],
  [s47, s98, s150, s258, s279, s302, s321, s336],
  [s47, s150, s247, s302, s321, s336, s350]]
def b8_13 : List (List Sig) := [
  [s4, s8, s47, s150, s258, s302, s321, s336],
  [s8, s21, s47, s150, s258, s302, s321, s336],
  [s8, s29, s47, s150, s258, s302, s321, s336],
  [s8, s47, s82, s150, s258, s302, s321, s336],
  [s8, s47, s150, s168, s258, s302, s321, s336],
  [s8, s47, s150, s183, s258, s302, s321, s336],
  [s47, s109, s111, s150, s258, s302, s321, s336],
  [s47, s111, s140, s150, s258, s302, s321, s336],
  [s47, s111, s150, s247, s258, s302, s321, s336],
  [s47, s111, s150, s258, s302, s321, s329, s336]]
def b8_14 : List (List Sig) := [
  [s8, s47, s150, s258, s302, s321, s336],
  [s21, s47, s150, s160, s258, s302, s321],
  [s24, s47, s150, s258, s302, s321, s336],
  [s47, s84, s150, s258, s302, s321, s336],
  [s47, s99, s150, s258, s302, s321, s336]]
def b8_15 : List (List Sig) := [
  [s0, s47, s150, s258, s302, s321, s336],
  [s8, s32, s47, s150, s258, s302, s321, s336],
  [s8, s47, s69, s258, s302, s321, s336],
  [s8, s47, s150, s241, s258, s302, s321, s336],
  [s17, s21, s47, s150, s258, s302, s321, s336],
  [s17, s47, s69, s150, s302, s321, s336],
  [s17, s47, s82, s150, s258, s302, s321, s336],
  [s17, s47, s150, s258, s302, s323, s336],
  [s18, s47, s150, s258, s302, s321, s336]]
def b8_16 : List (List Sig) := [
  [s17, s47, s150, s258, s302, s321, s336],
  [s21, s47, s129, s150, s258, s302, s321],
  [s31, s47, s150, s258, s302, s321, s336],
  [s33, s47, s150, s258, s302, s315, s321, s336],
  [s47, s150, s163, s258, s302, s321, s336],
  [s47, s150, s184, s258, s302, s321, s336]]
def b8_17 : List (List Sig) := [
  [s16, s47, s150, s258, s302, s321, s336],
  [s17, s39, s150, s258, s302, s321, s336],
  [s17, s47, s150, s228, s302, s321, s336],
  [s17, s47, s150, s270, s302, s321, s336]]
def b8_18 : List (List Sig) := [
  [s1, s47, s150, s258, s302, s321, s336],
  [s8, s32, s150, s258, s302, s321, s336],
  [s8, s47, s111, s258, s302, s321, s336],
  [s47, s51, s111, s150, s258, s302, s321, s336],
  [s47, s69, s150, s302, s321, s336, s350]]
def b8_19 : List (List Sig) := [
  [s8, s47, s150, s258, s300, s302, s321, s336],
  [s8, s47, s258, s289, s302, s321, s336],
  [s33, s150, s258, s302, s315, s321, s336],
  [s47, s69, s111, s150, s258, s302, s321, s336],
  [s47, s75, s150, s157, s302, s321, s336],
  [s47, s76, s150, s258, s302, s321, s336],
  [s47, s98, s111, s150, s258, s302, s321, s336],
  [s47, s113, s258, s302, s304, s321, s336],
  [s47, s115, s150, s258, s302, s321, s336],
  [s47, s139, s258, s302, s321, s336, s353],
  [s47, s150, s155, s258, s302, s321, s336],
  [s47, s150, s157, s258, s302, s321, s336],
  [s47, s150, s160, s174, s258, s302, s321],
  [s47, s150, s191, s302, s321, s336],
  [s47, s150, s217, s302, s315, s321, s336],
  [s47, s150, s258, s288, s302, s321, s336],
  [s47, s150, s258, s302, s315, s321, s336]]
def b8_20 : List (List Sig) := [
  [s0, s8, s47, s150, s258, s302, s321, s336],
  [s47, s82, s150, s258, s302, s321, s325]]
def b8_21 : List (List Sig) := [
  [s8, s17, s47, s150, s258, s302, s321, s336],
  [s21, s47, s140, s150, s258, s302, s321, s336],
  [s21, s47, s150, s247, s258, s302, s321, s336],
  [s21, s47, s150, s258, s302, s321, s329, s336],
  [s47, s82, s140, s150, s258, s302, s321, s336],
  [s47, s82, s150, s247, s258, s302, s321, s336],
  [s47, s82, s150, s258, s297, s302, s321, s336],
  [s47, s82, s150, s258, s302, s321, s329, s336],
  [s47, s111, s150, s228, s258, s302, s321, s336],
  [s47, s145, s150, s258, s302, s321, s336],
  [s47, s150, s160, s258, s302, s324, s336],
  [s47, s150, s250, s258, s302, s321, s336]]
def b8_22 : List (List Sig) := [
  [s47, s68, s150, s258, s302, s321, s336],
  [s47, s69, s258, s302, s318, s321, s336],
  [s47, s109, s150, s258, s302, s321, s336],
  [s47, s140, s150, s258, s302, s321, s336],
  [s47, s150, s227, s258, s302, s321, s336],
  [s47, s150, s247, s258, s302, s321, s336],
  [s47, s150, s258, s265, s302, s321, s336],
  [s47, s150, s258, s302, s309, s321, s336],
  [s47, s150, s258, s302, s321, s336, s348]]
def b8_23 : List (List Sig) := [
  [s1, s8, s47, s150, s258, s302, s321, s336],
  [s47, s69, s150, s258, s274, s302, s321, s336]]
def b8_24 : List (List Sig) := [
  [s8, s47, s150, s157, s258, s302, s321, s336],
  [s8, s47, s150, s258, s263, s302, s321, s336],
  [s8, s47, s150, s258, s302, s303, s321, s336],
  [s8, s47, s150, s258, s302, s304, s321, s336],
  [s8, s47, s150, s258, s302, s315, s321, s336],
  [s8, s47, s150, s258, s302, s321, s336, s350],
  [s8, s47, s150, s258, s302, s321, s336, s353],
  [s21, s150, s258, s302, s321, s329, s336]]
def b8_25 : List (List Sig) := [
  [s30, s47, s150, s258, s302, s321, s336],
  [s150, s258, s302, s309, s321, s336],
  [s150, s258, s302, s321, s336, s348]]
def b8_26 : List (List Sig) := [
  [s14, s47, s150, s258, s302, s321, s336],
  [s17, s47, s133, s150, s302, s321, s336],
  [s17, s47, s150, s258, s302, s315, s321, s336],
  [s47, s59, s150, s258, s302, s321, s336],
  [s47, s150, s160, s258, s302, s321, s336]]
def b8_27 : List (List Sig) := [
  [s8, s47, s140, s150, s258, s302, s321, s336],
  [s8, s47, s150, s247, s258, s302, s321, s336],
  [s8, s47, s150, s258, s297, s302, s321, s336],
  [s8, s150, s157, s258, s302, s321, s336],
  [s21, s47, s69, s150, s258, s302, s321, s336],
  [s21, s47, s82, s150, s258, s302, s321],
  [s29, s47, s126, s150, s258, s302, s336],
  [s47, s51, s150, s258, s302, s321, s336],
  [s47, s69, s82, s150, s258, s302, s321, s336],
  [s47, s69, s150, s168, s258, s302, s321, s336],
  [s47, s69, s150, s211, s302, s321, s336],
  [s47, s69, s150, s268, s302, s321, s336],
  [s47, s72, s150, s258, s302, s321, s336],
  [s47, s82, s150, s168, s258, s302, s321],
  [s47, s84, s150, s258, s302, s321, s329, s336],
  [s47, s99, s150, s258, s302, s319, s321, s336],
  [s47, s111, s150, s258, s315, s321, s336],
  [s47, s113, s150, s258, s302, s321, s336],
  [s47, s128, s150, s258, s302, s321, s336],
  [s47, s139, s150, s258, s302, s321, s336],
  [s47, s150, s153, s258, s302, s321, s336],
  [s47, s150, s180, s258, s302, s321, s336],
  [s47, s150, s182, s258, s302, s321, s336],
  [s47, s150, s225, s258, s302, s321, s336],
  [s47, s150, s258, s266, s302, s321, s336],
  [s47, s150, s258, s302, s311, s321, s336]]
def b8_28 : List (List Sig) := [
  [s8, s47, s150, s255, s258, s302, s321, s336],
  [s8, s47, s241, s258, s302, s321, s336],
  [s47, s69, s150, s258, s302, s321, s336],
  [s47, s85, s150, s258, s302, s321],
  [s47, s100, s150, s258, s302, s336],
  [s47, s103, s150, s258, s302, s321, s336],
  [s47, s141, s150, s258, s302, s321, s336],
  [s47, s150, s151, s258, s302, s321, s336],
  [s47, s150, s164, s258, s302, s321],
  [s47, s150, s166, s258, s302, s321, s336],
  [s47, s150, s176, s258, s302, s321],
  [s47, s150, s177, s258, s302, s321],
  [s47, s150, s185, s258, s302, s336],
  [s47, s150, s201, s258, s302, s336],
  [s47, s150, s219, s258, s302, s321, s336],
  [s47, s150, s248, s258, s302, s321, s336]]
def b8_29 : List (List Sig) := [
  [s8, s47, s150, s258, s279, s302, s321, s336],
  [s8, s47, s150, s258, s302, s321, s336, s346],
  [s25, s47, s150, s258, s302, s321, s336],
  [s47, s75, s150, s258, s302, s321, s336]]
def b8_30 : List (List Sig) := [
  [s8, s150, s258, s297, s302, s321, s336],
  [s29, s47, s111, s150, s258, s302, s321, s336],
  [s47, s111, s150, s183, s258, s302, s321, s336],
  [s47, s150, s207, s258, s302, s321, s336]]
def bucketTier8 : List (List (List Sig)) := [b8_0, b8_1, b8_2, b8_3, b8_4, b8_5, b8_6, b8_7, b8_8, b8_9, b8_10, b8_11, b8_12, b8_13, b8_14, b8_15, b8_16, b8_17, b8_18, b8_19, b8_20, b8_21, b8_22, b8_23, b8_24, b8_25, b8_26, b8_27, b8_28, b8_29, b8_30]

def b9_0 : List (List Sig) := [
  [s47, s111, s150, s258, s302, s321, s336]]
def b9_8 : List (List Sig) := [
  [s21, s47, s150, s258, s302, s321, s336],
  [s29, s47, s150, s258, s302, s321, s336],
  [s47, s82, s150, s258, s302, s321, s336],
  [s47, s150, s183, s258, s302, s321, s336]]
def b9_14 : List (List Sig) := [
  [s8, s47, s150, s258, s302, s321, s336]]
def b9_16 : List (List Sig) := [
  [s17, s47, s150, s258, s302, s321, s336]]
def b9_19 : List (List Sig) := [
  [s47, s150, s157, s258, s302, s321, s336],
  [s47, s150, s258, s263, s302, s321, s336],
  [s47, s150, s258, s302, s315, s321, s336],
  [s47, s150, s258, s302, s321, s336, s350]]
def b9_22 : List (List Sig) := [
  [s47, s140, s150, s258, s302, s321, s336],
  [s47, s150, s247, s258, s302, s321, s336]]
def b9_26 : List (List Sig) := [
  [s47, s150, s160, s258, s302, s321, s336]]
def b9_28 : List (List Sig) := [
  [s47, s69, s150, s258, s302, s321, s336],
  [s47, s98, s150, s258, s302, s321, s336],
  [s47, s150, s258, s268, s302, s321, s336]]
def b9_30 : List (List Sig) := [
  [s47, s150, s228, s258, s302, s321, s336]]
def bucketTier9 : List (List (List Sig)) := [b9_0, [], [], [], [], [], [], [], b9_8, [], [], [], [], [], b9_14, [], b9_16, [], [], b9_19, [], [], b9_22, [], [], [], b9_26, [], b9_28, [], b9_30]

def b10_9 : List (List Sig) := [
  [s47, s150, s258, s302, s321, s336]]
def bucketTier10 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], b10_9, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def buckets : ℕ → List (List (List Sig))
  | 1 => bucketTier1
  | 2 => bucketTier2
  | 3 => bucketTier3
  | 4 => bucketTier4
  | 5 => bucketTier5
  | 6 => bucketTier6
  | 7 => bucketTier7
  | 8 => bucketTier8
  | 9 => bucketTier9
  | 10 => bucketTier10
  | _ => []

def tiers (n : ℕ) : List (List Sig) := (buckets n).flatten
def lookup (n : ℕ) (w : List Sig) : Bool := bucketHas w (buckets n) (hashBucket w)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma lookup_sound (n : ℕ) (w : List Sig) (h : lookup n w = true) : w ∈ tiers n :=
  bucketHas_sound w _ _ h

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma startND : (minorRaw (5 : Fin 7)).Nodup := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma sortedStart : sortSignals (minorRaw (5 : Fin 7)) ∈ tiers 10 := by decide +kernel
end Minor5


namespace Minor0
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma group_valid : GroupGood group := group_checked (by decide +kernel)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level1 : checkRows chart16 group 0 (lookup 0) (tiers 1) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level2 : checkRows chart16 group 1 (lookup 1) (tiers 2) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level3 : checkRows chart16 group 2 (lookup 2) (tiers 3) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_8 : checkRows chart16 group 3 (lookup 3) b4_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level4 : checkRows chart16 group 3 (lookup 3) (tiers 4) = true := by
  simp only [tiers, buckets, bucketTier4, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb4_8]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_3 : checkRows chart16 group 4 (lookup 4) b5_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_4 : checkRows chart16 group 4 (lookup 4) b5_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_5 : checkRows chart16 group 4 (lookup 4) b5_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_6 : checkRows chart16 group 4 (lookup 4) b5_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_14 : checkRows chart16 group 4 (lookup 4) b5_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_15 : checkRows chart16 group 4 (lookup 4) b5_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_18 : checkRows chart16 group 4 (lookup 4) b5_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_23 : checkRows chart16 group 4 (lookup 4) b5_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_24 : checkRows chart16 group 4 (lookup 4) b5_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_25 : checkRows chart16 group 4 (lookup 4) b5_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_29 : checkRows chart16 group 4 (lookup 4) b5_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level5 : checkRows chart16 group 4 (lookup 4) (tiers 5) = true := by
  simp only [tiers, buckets, bucketTier5, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb5_3, cb5_4, cb5_5, cb5_6, cb5_14, cb5_15, cb5_18, cb5_23, cb5_24, cb5_25, cb5_29]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_0 : checkRows chart16 group 5 (lookup 5) b6_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_1 : checkRows chart16 group 5 (lookup 5) b6_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_2 : checkRows chart16 group 5 (lookup 5) b6_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_3 : checkRows chart16 group 5 (lookup 5) b6_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_4 : checkRows chart16 group 5 (lookup 5) b6_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_5 : checkRows chart16 group 5 (lookup 5) b6_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_6 : checkRows chart16 group 5 (lookup 5) b6_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_7 : checkRows chart16 group 5 (lookup 5) b6_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_8 : checkRows chart16 group 5 (lookup 5) b6_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_9 : checkRows chart16 group 5 (lookup 5) b6_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_10 : checkRows chart16 group 5 (lookup 5) b6_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_11 : checkRows chart16 group 5 (lookup 5) b6_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_13 : checkRows chart16 group 5 (lookup 5) b6_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_14 : checkRows chart16 group 5 (lookup 5) b6_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_15 : checkRows chart16 group 5 (lookup 5) b6_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_16 : checkRows chart16 group 5 (lookup 5) b6_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_17 : checkRows chart16 group 5 (lookup 5) b6_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_18 : checkRows chart16 group 5 (lookup 5) b6_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_19 : checkRows chart16 group 5 (lookup 5) b6_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_20 : checkRows chart16 group 5 (lookup 5) b6_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_21 : checkRows chart16 group 5 (lookup 5) b6_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_22 : checkRows chart16 group 5 (lookup 5) b6_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_23 : checkRows chart16 group 5 (lookup 5) b6_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_24 : checkRows chart16 group 5 (lookup 5) b6_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_25 : checkRows chart16 group 5 (lookup 5) b6_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_26 : checkRows chart16 group 5 (lookup 5) b6_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_27 : checkRows chart16 group 5 (lookup 5) b6_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_28 : checkRows chart16 group 5 (lookup 5) b6_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_29 : checkRows chart16 group 5 (lookup 5) b6_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_30 : checkRows chart16 group 5 (lookup 5) b6_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level6 : checkRows chart16 group 5 (lookup 5) (tiers 6) = true := by
  simp only [tiers, buckets, bucketTier6, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb6_0, cb6_1, cb6_2, cb6_3, cb6_4, cb6_5, cb6_6, cb6_7, cb6_8, cb6_9, cb6_10, cb6_11, cb6_13, cb6_14, cb6_15, cb6_16, cb6_17, cb6_18, cb6_19, cb6_20, cb6_21, cb6_22, cb6_23, cb6_24, cb6_25, cb6_26, cb6_27, cb6_28, cb6_29, cb6_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_0 : checkRows chart16 group 6 (lookup 6) b7_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_1 : checkRows chart16 group 6 (lookup 6) b7_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_2 : checkRows chart16 group 6 (lookup 6) b7_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_3 : checkRows chart16 group 6 (lookup 6) b7_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_4 : checkRows chart16 group 6 (lookup 6) b7_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_5 : checkRows chart16 group 6 (lookup 6) b7_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_6 : checkRows chart16 group 6 (lookup 6) b7_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_7 : checkRows chart16 group 6 (lookup 6) b7_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_8 : checkRows chart16 group 6 (lookup 6) b7_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_9 : checkRows chart16 group 6 (lookup 6) b7_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_10 : checkRows chart16 group 6 (lookup 6) b7_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_11 : checkRows chart16 group 6 (lookup 6) b7_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_12 : checkRows chart16 group 6 (lookup 6) b7_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_13 : checkRows chart16 group 6 (lookup 6) b7_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_14 : checkRows chart16 group 6 (lookup 6) b7_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_15 : checkRows chart16 group 6 (lookup 6) b7_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_16 : checkRows chart16 group 6 (lookup 6) b7_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_17 : checkRows chart16 group 6 (lookup 6) b7_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_18 : checkRows chart16 group 6 (lookup 6) b7_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_19 : checkRows chart16 group 6 (lookup 6) b7_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_20 : checkRows chart16 group 6 (lookup 6) b7_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_21 : checkRows chart16 group 6 (lookup 6) b7_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_22 : checkRows chart16 group 6 (lookup 6) b7_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_23 : checkRows chart16 group 6 (lookup 6) b7_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_24 : checkRows chart16 group 6 (lookup 6) b7_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_25 : checkRows chart16 group 6 (lookup 6) b7_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_26 : checkRows chart16 group 6 (lookup 6) b7_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_27 : checkRows chart16 group 6 (lookup 6) b7_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_28 : checkRows chart16 group 6 (lookup 6) b7_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_29 : checkRows chart16 group 6 (lookup 6) b7_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_30 : checkRows chart16 group 6 (lookup 6) b7_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level7 : checkRows chart16 group 6 (lookup 6) (tiers 7) = true := by
  simp only [tiers, buckets, bucketTier7, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb7_0, cb7_1, cb7_2, cb7_3, cb7_4, cb7_5, cb7_6, cb7_7, cb7_8, cb7_9, cb7_10, cb7_11, cb7_12, cb7_13, cb7_14, cb7_15, cb7_16, cb7_17, cb7_18, cb7_19, cb7_20, cb7_21, cb7_22, cb7_23, cb7_24, cb7_25, cb7_26, cb7_27, cb7_28, cb7_29, cb7_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_1 : checkRows chart16 group 7 (lookup 7) b8_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_3 : checkRows chart16 group 7 (lookup 7) b8_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_4 : checkRows chart16 group 7 (lookup 7) b8_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_5 : checkRows chart16 group 7 (lookup 7) b8_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_6 : checkRows chart16 group 7 (lookup 7) b8_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_7 : checkRows chart16 group 7 (lookup 7) b8_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_8 : checkRows chart16 group 7 (lookup 7) b8_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_10 : checkRows chart16 group 7 (lookup 7) b8_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_11 : checkRows chart16 group 7 (lookup 7) b8_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_12 : checkRows chart16 group 7 (lookup 7) b8_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_13 : checkRows chart16 group 7 (lookup 7) b8_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_14 : checkRows chart16 group 7 (lookup 7) b8_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_15 : checkRows chart16 group 7 (lookup 7) b8_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_16 : checkRows chart16 group 7 (lookup 7) b8_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_17 : checkRows chart16 group 7 (lookup 7) b8_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_18 : checkRows chart16 group 7 (lookup 7) b8_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_19 : checkRows chart16 group 7 (lookup 7) b8_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_20 : checkRows chart16 group 7 (lookup 7) b8_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_21 : checkRows chart16 group 7 (lookup 7) b8_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_22 : checkRows chart16 group 7 (lookup 7) b8_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_23 : checkRows chart16 group 7 (lookup 7) b8_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_24 : checkRows chart16 group 7 (lookup 7) b8_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_25 : checkRows chart16 group 7 (lookup 7) b8_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_26 : checkRows chart16 group 7 (lookup 7) b8_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_27 : checkRows chart16 group 7 (lookup 7) b8_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_28 : checkRows chart16 group 7 (lookup 7) b8_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_30 : checkRows chart16 group 7 (lookup 7) b8_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level8 : checkRows chart16 group 7 (lookup 7) (tiers 8) = true := by
  simp only [tiers, buckets, bucketTier8, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb8_1, cb8_3, cb8_4, cb8_5, cb8_6, cb8_7, cb8_8, cb8_10, cb8_11, cb8_12, cb8_13, cb8_14, cb8_15, cb8_16, cb8_17, cb8_18, cb8_19, cb8_20, cb8_21, cb8_22, cb8_23, cb8_24, cb8_25, cb8_26, cb8_27, cb8_28, cb8_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_1 : checkRows chart16 group 8 (lookup 8) b9_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_5 : checkRows chart16 group 8 (lookup 8) b9_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_7 : checkRows chart16 group 8 (lookup 8) b9_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_14 : checkRows chart16 group 8 (lookup 8) b9_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_15 : checkRows chart16 group 8 (lookup 8) b9_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_24 : checkRows chart16 group 8 (lookup 8) b9_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_25 : checkRows chart16 group 8 (lookup 8) b9_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_30 : checkRows chart16 group 8 (lookup 8) b9_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level9 : checkRows chart16 group 8 (lookup 8) (tiers 9) = true := by
  simp only [tiers, buckets, bucketTier9, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb9_1, cb9_5, cb9_7, cb9_14, cb9_15, cb9_24, cb9_25, cb9_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb10_15 : checkRows chart16 group 9 (lookup 9) b10_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level10 : checkRows chart16 group 9 (lookup 9) (tiers 10) = true := by
  simp only [tiers, buckets, bucketTier10, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb10_15]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified0 : verified tiers 0 := verificationStart rfl
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified1 : verified tiers 1 := verificationStep chart_valid16 group_valid
  (lookup_sound 0) verified0 level1
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified2 : verified tiers 2 := verificationStep chart_valid16 group_valid
  (lookup_sound 1) verified1 level2
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified3 : verified tiers 3 := verificationStep chart_valid16 group_valid
  (lookup_sound 2) verified2 level3
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified4 : verified tiers 4 := verificationStep chart_valid16 group_valid
  (lookup_sound 3) verified3 level4
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified5 : verified tiers 5 := verificationStep chart_valid16 group_valid
  (lookup_sound 4) verified4 level5
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified6 : verified tiers 6 := verificationStep chart_valid16 group_valid
  (lookup_sound 5) verified5 level6
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified7 : verified tiers 7 := verificationStep chart_valid16 group_valid
  (lookup_sound 6) verified6 level7
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified8 : verified tiers 8 := verificationStep chart_valid16 group_valid
  (lookup_sound 7) verified7 level8
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified9 : verified tiers 9 := verificationStep chart_valid16 group_valid
  (lookup_sound 8) verified8 level9
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified10 : verified tiers 10 := verificationStep chart_valid16 group_valid
  (lookup_sound 9) verified9 level10

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma noMinor {m : Nat} (cap : m ≤ 10) : ¬ BL m (minorRaw (0 : Fin 7)).toFinset := by
  intro live
  exact verified10 _ sortedStart ((sort_perm _).nodup_iff.mpr startND) m cap
    ((sort_set _).symm ▸ live)
end Minor0


namespace Minor1
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma group_valid : GroupGood group := group_checked (by decide +kernel)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level1 : checkRows chart16 group 0 (lookup 0) (tiers 1) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level2 : checkRows chart16 group 1 (lookup 1) (tiers 2) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level3 : checkRows chart16 group 2 (lookup 2) (tiers 3) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_3 : checkRows chart16 group 3 (lookup 3) b4_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_5 : checkRows chart16 group 3 (lookup 3) b4_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_7 : checkRows chart16 group 3 (lookup 3) b4_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_12 : checkRows chart16 group 3 (lookup 3) b4_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_17 : checkRows chart16 group 3 (lookup 3) b4_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_19 : checkRows chart16 group 3 (lookup 3) b4_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_27 : checkRows chart16 group 3 (lookup 3) b4_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level4 : checkRows chart16 group 3 (lookup 3) (tiers 4) = true := by
  simp only [tiers, buckets, bucketTier4, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb4_3, cb4_5, cb4_7, cb4_12, cb4_17, cb4_19, cb4_27]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_0 : checkRows chart16 group 4 (lookup 4) b5_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_1 : checkRows chart16 group 4 (lookup 4) b5_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_3 : checkRows chart16 group 4 (lookup 4) b5_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_4 : checkRows chart16 group 4 (lookup 4) b5_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_5 : checkRows chart16 group 4 (lookup 4) b5_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_6 : checkRows chart16 group 4 (lookup 4) b5_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_7 : checkRows chart16 group 4 (lookup 4) b5_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_8 : checkRows chart16 group 4 (lookup 4) b5_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_9 : checkRows chart16 group 4 (lookup 4) b5_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_12 : checkRows chart16 group 4 (lookup 4) b5_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_13 : checkRows chart16 group 4 (lookup 4) b5_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_14 : checkRows chart16 group 4 (lookup 4) b5_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_15 : checkRows chart16 group 4 (lookup 4) b5_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_16 : checkRows chart16 group 4 (lookup 4) b5_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_17 : checkRows chart16 group 4 (lookup 4) b5_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_19 : checkRows chart16 group 4 (lookup 4) b5_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_22 : checkRows chart16 group 4 (lookup 4) b5_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_24 : checkRows chart16 group 4 (lookup 4) b5_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_25 : checkRows chart16 group 4 (lookup 4) b5_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_26 : checkRows chart16 group 4 (lookup 4) b5_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_27 : checkRows chart16 group 4 (lookup 4) b5_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_28 : checkRows chart16 group 4 (lookup 4) b5_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_29 : checkRows chart16 group 4 (lookup 4) b5_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_30 : checkRows chart16 group 4 (lookup 4) b5_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level5 : checkRows chart16 group 4 (lookup 4) (tiers 5) = true := by
  simp only [tiers, buckets, bucketTier5, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb5_0, cb5_1, cb5_3, cb5_4, cb5_5, cb5_6, cb5_7, cb5_8, cb5_9, cb5_12, cb5_13, cb5_14, cb5_15, cb5_16, cb5_17, cb5_19, cb5_22, cb5_24, cb5_25, cb5_26, cb5_27, cb5_28, cb5_29, cb5_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_0 : checkRows chart16 group 5 (lookup 5) b6_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_1 : checkRows chart16 group 5 (lookup 5) b6_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_2 : checkRows chart16 group 5 (lookup 5) b6_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_3 : checkRows chart16 group 5 (lookup 5) b6_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_4 : checkRows chart16 group 5 (lookup 5) b6_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_5 : checkRows chart16 group 5 (lookup 5) b6_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_6 : checkRows chart16 group 5 (lookup 5) b6_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_7 : checkRows chart16 group 5 (lookup 5) b6_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_8 : checkRows chart16 group 5 (lookup 5) b6_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_9 : checkRows chart16 group 5 (lookup 5) b6_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_10 : checkRows chart16 group 5 (lookup 5) b6_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_11 : checkRows chart16 group 5 (lookup 5) b6_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_12 : checkRows chart16 group 5 (lookup 5) b6_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_13 : checkRows chart16 group 5 (lookup 5) b6_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_14 : checkRows chart16 group 5 (lookup 5) b6_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_15 : checkRows chart16 group 5 (lookup 5) b6_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_16 : checkRows chart16 group 5 (lookup 5) b6_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_17 : checkRows chart16 group 5 (lookup 5) b6_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_18 : checkRows chart16 group 5 (lookup 5) b6_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_19 : checkRows chart16 group 5 (lookup 5) b6_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_20 : checkRows chart16 group 5 (lookup 5) b6_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_21 : checkRows chart16 group 5 (lookup 5) b6_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_22 : checkRows chart16 group 5 (lookup 5) b6_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_23 : checkRows chart16 group 5 (lookup 5) b6_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_24 : checkRows chart16 group 5 (lookup 5) b6_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_25 : checkRows chart16 group 5 (lookup 5) b6_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_26 : checkRows chart16 group 5 (lookup 5) b6_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_27 : checkRows chart16 group 5 (lookup 5) b6_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_28 : checkRows chart16 group 5 (lookup 5) b6_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_29 : checkRows chart16 group 5 (lookup 5) b6_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_30 : checkRows chart16 group 5 (lookup 5) b6_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level6 : checkRows chart16 group 5 (lookup 5) (tiers 6) = true := by
  simp only [tiers, buckets, bucketTier6, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb6_0, cb6_1, cb6_2, cb6_3, cb6_4, cb6_5, cb6_6, cb6_7, cb6_8, cb6_9, cb6_10, cb6_11, cb6_12, cb6_13, cb6_14, cb6_15, cb6_16, cb6_17, cb6_18, cb6_19, cb6_20, cb6_21, cb6_22, cb6_23, cb6_24, cb6_25, cb6_26, cb6_27, cb6_28, cb6_29, cb6_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_0 : checkRows chart16 group 6 (lookup 6) b7_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_1 : checkRows chart16 group 6 (lookup 6) b7_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_2 : checkRows chart16 group 6 (lookup 6) b7_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_3 : checkRows chart16 group 6 (lookup 6) b7_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_4 : checkRows chart16 group 6 (lookup 6) b7_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_5 : checkRows chart16 group 6 (lookup 6) b7_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_6 : checkRows chart16 group 6 (lookup 6) b7_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_7 : checkRows chart16 group 6 (lookup 6) b7_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_8 : checkRows chart16 group 6 (lookup 6) b7_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_9 : checkRows chart16 group 6 (lookup 6) b7_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_10 : checkRows chart16 group 6 (lookup 6) b7_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_11 : checkRows chart16 group 6 (lookup 6) b7_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_12 : checkRows chart16 group 6 (lookup 6) b7_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_13 : checkRows chart16 group 6 (lookup 6) b7_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_14 : checkRows chart16 group 6 (lookup 6) b7_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_15 : checkRows chart16 group 6 (lookup 6) b7_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_16 : checkRows chart16 group 6 (lookup 6) b7_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_17 : checkRows chart16 group 6 (lookup 6) b7_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_18 : checkRows chart16 group 6 (lookup 6) b7_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_19 : checkRows chart16 group 6 (lookup 6) b7_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_20 : checkRows chart16 group 6 (lookup 6) b7_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_21 : checkRows chart16 group 6 (lookup 6) b7_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_22 : checkRows chart16 group 6 (lookup 6) b7_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_23 : checkRows chart16 group 6 (lookup 6) b7_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_24 : checkRows chart16 group 6 (lookup 6) b7_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_25 : checkRows chart16 group 6 (lookup 6) b7_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_26 : checkRows chart16 group 6 (lookup 6) b7_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_27 : checkRows chart16 group 6 (lookup 6) b7_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_28 : checkRows chart16 group 6 (lookup 6) b7_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_29 : checkRows chart16 group 6 (lookup 6) b7_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_30 : checkRows chart16 group 6 (lookup 6) b7_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level7 : checkRows chart16 group 6 (lookup 6) (tiers 7) = true := by
  simp only [tiers, buckets, bucketTier7, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb7_0, cb7_1, cb7_2, cb7_3, cb7_4, cb7_5, cb7_6, cb7_7, cb7_8, cb7_9, cb7_10, cb7_11, cb7_12, cb7_13, cb7_14, cb7_15, cb7_16, cb7_17, cb7_18, cb7_19, cb7_20, cb7_21, cb7_22, cb7_23, cb7_24, cb7_25, cb7_26, cb7_27, cb7_28, cb7_29, cb7_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_0 : checkRows chart16 group 7 (lookup 7) b8_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_1 : checkRows chart16 group 7 (lookup 7) b8_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_2 : checkRows chart16 group 7 (lookup 7) b8_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_3 : checkRows chart16 group 7 (lookup 7) b8_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_4 : checkRows chart16 group 7 (lookup 7) b8_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_5 : checkRows chart16 group 7 (lookup 7) b8_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_6 : checkRows chart16 group 7 (lookup 7) b8_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_7 : checkRows chart16 group 7 (lookup 7) b8_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_8 : checkRows chart16 group 7 (lookup 7) b8_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_9 : checkRows chart16 group 7 (lookup 7) b8_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_10 : checkRows chart16 group 7 (lookup 7) b8_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_11 : checkRows chart16 group 7 (lookup 7) b8_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_12 : checkRows chart16 group 7 (lookup 7) b8_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_14 : checkRows chart16 group 7 (lookup 7) b8_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_15 : checkRows chart16 group 7 (lookup 7) b8_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_16 : checkRows chart16 group 7 (lookup 7) b8_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_17 : checkRows chart16 group 7 (lookup 7) b8_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_18 : checkRows chart16 group 7 (lookup 7) b8_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_19 : checkRows chart16 group 7 (lookup 7) b8_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_20 : checkRows chart16 group 7 (lookup 7) b8_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_21 : checkRows chart16 group 7 (lookup 7) b8_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_22 : checkRows chart16 group 7 (lookup 7) b8_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_23 : checkRows chart16 group 7 (lookup 7) b8_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_24 : checkRows chart16 group 7 (lookup 7) b8_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_25 : checkRows chart16 group 7 (lookup 7) b8_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_26 : checkRows chart16 group 7 (lookup 7) b8_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_27 : checkRows chart16 group 7 (lookup 7) b8_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_29 : checkRows chart16 group 7 (lookup 7) b8_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_30 : checkRows chart16 group 7 (lookup 7) b8_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level8 : checkRows chart16 group 7 (lookup 7) (tiers 8) = true := by
  simp only [tiers, buckets, bucketTier8, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb8_0, cb8_1, cb8_2, cb8_3, cb8_4, cb8_5, cb8_6, cb8_7, cb8_8, cb8_9, cb8_10, cb8_11, cb8_12, cb8_14, cb8_15, cb8_16, cb8_17, cb8_18, cb8_19, cb8_20, cb8_21, cb8_22, cb8_23, cb8_24, cb8_25, cb8_26, cb8_27, cb8_29, cb8_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_4 : checkRows chart16 group 8 (lookup 8) b9_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_5 : checkRows chart16 group 8 (lookup 8) b9_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_6 : checkRows chart16 group 8 (lookup 8) b9_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_7 : checkRows chart16 group 8 (lookup 8) b9_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_8 : checkRows chart16 group 8 (lookup 8) b9_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_11 : checkRows chart16 group 8 (lookup 8) b9_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_17 : checkRows chart16 group 8 (lookup 8) b9_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_20 : checkRows chart16 group 8 (lookup 8) b9_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_21 : checkRows chart16 group 8 (lookup 8) b9_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level9 : checkRows chart16 group 8 (lookup 8) (tiers 9) = true := by
  simp only [tiers, buckets, bucketTier9, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb9_4, cb9_5, cb9_6, cb9_7, cb9_8, cb9_11, cb9_17, cb9_20, cb9_21]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb10_26 : checkRows chart16 group 9 (lookup 9) b10_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level10 : checkRows chart16 group 9 (lookup 9) (tiers 10) = true := by
  simp only [tiers, buckets, bucketTier10, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb10_26]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified0 : verified tiers 0 := verificationStart rfl
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified1 : verified tiers 1 := verificationStep chart_valid16 group_valid
  (lookup_sound 0) verified0 level1
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified2 : verified tiers 2 := verificationStep chart_valid16 group_valid
  (lookup_sound 1) verified1 level2
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified3 : verified tiers 3 := verificationStep chart_valid16 group_valid
  (lookup_sound 2) verified2 level3
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified4 : verified tiers 4 := verificationStep chart_valid16 group_valid
  (lookup_sound 3) verified3 level4
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified5 : verified tiers 5 := verificationStep chart_valid16 group_valid
  (lookup_sound 4) verified4 level5
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified6 : verified tiers 6 := verificationStep chart_valid16 group_valid
  (lookup_sound 5) verified5 level6
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified7 : verified tiers 7 := verificationStep chart_valid16 group_valid
  (lookup_sound 6) verified6 level7
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified8 : verified tiers 8 := verificationStep chart_valid16 group_valid
  (lookup_sound 7) verified7 level8
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified9 : verified tiers 9 := verificationStep chart_valid16 group_valid
  (lookup_sound 8) verified8 level9
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified10 : verified tiers 10 := verificationStep chart_valid16 group_valid
  (lookup_sound 9) verified9 level10

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma noMinor {m : Nat} (cap : m ≤ 10) : ¬ BL m (minorRaw (1 : Fin 7)).toFinset := by
  intro live
  exact verified10 _ sortedStart ((sort_perm _).nodup_iff.mpr startND) m cap
    ((sort_set _).symm ▸ live)
end Minor1


namespace Minor5
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma group_valid : GroupGood group := group_checked (by decide +kernel)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level1 : checkRows chart32 group 0 (lookup 0) (tiers 1) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level2 : checkRows chart32 group 1 (lookup 1) (tiers 2) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level3 : checkRows chart32 group 2 (lookup 2) (tiers 3) = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_12 : checkRows chart32 group 3 (lookup 3) b4_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb4_29 : checkRows chart32 group 3 (lookup 3) b4_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level4 : checkRows chart32 group 3 (lookup 3) (tiers 4) = true := by
  simp only [tiers, buckets, bucketTier4, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb4_12, cb4_29]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_4 : checkRows chart32 group 4 (lookup 4) b5_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_5 : checkRows chart32 group 4 (lookup 4) b5_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_6 : checkRows chart32 group 4 (lookup 4) b5_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_7 : checkRows chart32 group 4 (lookup 4) b5_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_8 : checkRows chart32 group 4 (lookup 4) b5_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_9 : checkRows chart32 group 4 (lookup 4) b5_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_12 : checkRows chart32 group 4 (lookup 4) b5_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_13 : checkRows chart32 group 4 (lookup 4) b5_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_14 : checkRows chart32 group 4 (lookup 4) b5_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_17 : checkRows chart32 group 4 (lookup 4) b5_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_20 : checkRows chart32 group 4 (lookup 4) b5_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_21 : checkRows chart32 group 4 (lookup 4) b5_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_22 : checkRows chart32 group 4 (lookup 4) b5_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_24 : checkRows chart32 group 4 (lookup 4) b5_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_27 : checkRows chart32 group 4 (lookup 4) b5_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb5_28 : checkRows chart32 group 4 (lookup 4) b5_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level5 : checkRows chart32 group 4 (lookup 4) (tiers 5) = true := by
  simp only [tiers, buckets, bucketTier5, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb5_4, cb5_5, cb5_6, cb5_7, cb5_8, cb5_9, cb5_12, cb5_13, cb5_14, cb5_17, cb5_20, cb5_21, cb5_22, cb5_24, cb5_27, cb5_28]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_0 : checkRows chart32 group 5 (lookup 5) b6_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_1 : checkRows chart32 group 5 (lookup 5) b6_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_2 : checkRows chart32 group 5 (lookup 5) b6_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_3 : checkRows chart32 group 5 (lookup 5) b6_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_4 : checkRows chart32 group 5 (lookup 5) b6_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_5 : checkRows chart32 group 5 (lookup 5) b6_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_6 : checkRows chart32 group 5 (lookup 5) b6_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_7 : checkRows chart32 group 5 (lookup 5) b6_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_8 : checkRows chart32 group 5 (lookup 5) b6_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_9 : checkRows chart32 group 5 (lookup 5) b6_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_11 : checkRows chart32 group 5 (lookup 5) b6_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_12 : checkRows chart32 group 5 (lookup 5) b6_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_13 : checkRows chart32 group 5 (lookup 5) b6_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_14 : checkRows chart32 group 5 (lookup 5) b6_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_15 : checkRows chart32 group 5 (lookup 5) b6_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_16 : checkRows chart32 group 5 (lookup 5) b6_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_17 : checkRows chart32 group 5 (lookup 5) b6_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_18 : checkRows chart32 group 5 (lookup 5) b6_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_19 : checkRows chart32 group 5 (lookup 5) b6_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_20 : checkRows chart32 group 5 (lookup 5) b6_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_21 : checkRows chart32 group 5 (lookup 5) b6_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_22 : checkRows chart32 group 5 (lookup 5) b6_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_23 : checkRows chart32 group 5 (lookup 5) b6_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_24 : checkRows chart32 group 5 (lookup 5) b6_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_25 : checkRows chart32 group 5 (lookup 5) b6_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_26 : checkRows chart32 group 5 (lookup 5) b6_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_27 : checkRows chart32 group 5 (lookup 5) b6_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_29 : checkRows chart32 group 5 (lookup 5) b6_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb6_30 : checkRows chart32 group 5 (lookup 5) b6_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level6 : checkRows chart32 group 5 (lookup 5) (tiers 6) = true := by
  simp only [tiers, buckets, bucketTier6, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb6_0, cb6_1, cb6_2, cb6_3, cb6_4, cb6_5, cb6_6, cb6_7, cb6_8, cb6_9, cb6_11, cb6_12, cb6_13, cb6_14, cb6_15, cb6_16, cb6_17, cb6_18, cb6_19, cb6_20, cb6_21, cb6_22, cb6_23, cb6_24, cb6_25, cb6_26, cb6_27, cb6_29, cb6_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_0 : checkRows chart32 group 6 (lookup 6) b7_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_1 : checkRows chart32 group 6 (lookup 6) b7_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_2 : checkRows chart32 group 6 (lookup 6) b7_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_3 : checkRows chart32 group 6 (lookup 6) b7_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_4 : checkRows chart32 group 6 (lookup 6) b7_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_5 : checkRows chart32 group 6 (lookup 6) b7_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_6 : checkRows chart32 group 6 (lookup 6) b7_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_7 : checkRows chart32 group 6 (lookup 6) b7_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_8 : checkRows chart32 group 6 (lookup 6) b7_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_9 : checkRows chart32 group 6 (lookup 6) b7_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_10 : checkRows chart32 group 6 (lookup 6) b7_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_11 : checkRows chart32 group 6 (lookup 6) b7_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_12 : checkRows chart32 group 6 (lookup 6) b7_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_13 : checkRows chart32 group 6 (lookup 6) b7_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_14 : checkRows chart32 group 6 (lookup 6) b7_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_15 : checkRows chart32 group 6 (lookup 6) b7_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_16 : checkRows chart32 group 6 (lookup 6) b7_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_17 : checkRows chart32 group 6 (lookup 6) b7_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_18 : checkRows chart32 group 6 (lookup 6) b7_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_19 : checkRows chart32 group 6 (lookup 6) b7_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_20 : checkRows chart32 group 6 (lookup 6) b7_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_21 : checkRows chart32 group 6 (lookup 6) b7_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_22 : checkRows chart32 group 6 (lookup 6) b7_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_23 : checkRows chart32 group 6 (lookup 6) b7_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_24 : checkRows chart32 group 6 (lookup 6) b7_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_25 : checkRows chart32 group 6 (lookup 6) b7_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_26 : checkRows chart32 group 6 (lookup 6) b7_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_27 : checkRows chart32 group 6 (lookup 6) b7_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_28 : checkRows chart32 group 6 (lookup 6) b7_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_29 : checkRows chart32 group 6 (lookup 6) b7_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb7_30 : checkRows chart32 group 6 (lookup 6) b7_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level7 : checkRows chart32 group 6 (lookup 6) (tiers 7) = true := by
  simp only [tiers, buckets, bucketTier7, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb7_0, cb7_1, cb7_2, cb7_3, cb7_4, cb7_5, cb7_6, cb7_7, cb7_8, cb7_9, cb7_10, cb7_11, cb7_12, cb7_13, cb7_14, cb7_15, cb7_16, cb7_17, cb7_18, cb7_19, cb7_20, cb7_21, cb7_22, cb7_23, cb7_24, cb7_25, cb7_26, cb7_27, cb7_28, cb7_29, cb7_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_0 : checkRows chart32 group 7 (lookup 7) b8_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_1 : checkRows chart32 group 7 (lookup 7) b8_1 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_2 : checkRows chart32 group 7 (lookup 7) b8_2 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_3 : checkRows chart32 group 7 (lookup 7) b8_3 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_4 : checkRows chart32 group 7 (lookup 7) b8_4 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_5 : checkRows chart32 group 7 (lookup 7) b8_5 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_6 : checkRows chart32 group 7 (lookup 7) b8_6 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_7 : checkRows chart32 group 7 (lookup 7) b8_7 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_8 : checkRows chart32 group 7 (lookup 7) b8_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_9 : checkRows chart32 group 7 (lookup 7) b8_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_10 : checkRows chart32 group 7 (lookup 7) b8_10 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_11 : checkRows chart32 group 7 (lookup 7) b8_11 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_12 : checkRows chart32 group 7 (lookup 7) b8_12 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_13 : checkRows chart32 group 7 (lookup 7) b8_13 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_14 : checkRows chart32 group 7 (lookup 7) b8_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_15 : checkRows chart32 group 7 (lookup 7) b8_15 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_16 : checkRows chart32 group 7 (lookup 7) b8_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_17 : checkRows chart32 group 7 (lookup 7) b8_17 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_18 : checkRows chart32 group 7 (lookup 7) b8_18 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_19 : checkRows chart32 group 7 (lookup 7) b8_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_20 : checkRows chart32 group 7 (lookup 7) b8_20 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_21 : checkRows chart32 group 7 (lookup 7) b8_21 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_22 : checkRows chart32 group 7 (lookup 7) b8_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_23 : checkRows chart32 group 7 (lookup 7) b8_23 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_24 : checkRows chart32 group 7 (lookup 7) b8_24 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_25 : checkRows chart32 group 7 (lookup 7) b8_25 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_26 : checkRows chart32 group 7 (lookup 7) b8_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_27 : checkRows chart32 group 7 (lookup 7) b8_27 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_28 : checkRows chart32 group 7 (lookup 7) b8_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_29 : checkRows chart32 group 7 (lookup 7) b8_29 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb8_30 : checkRows chart32 group 7 (lookup 7) b8_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level8 : checkRows chart32 group 7 (lookup 7) (tiers 8) = true := by
  simp only [tiers, buckets, bucketTier8, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb8_0, cb8_1, cb8_2, cb8_3, cb8_4, cb8_5, cb8_6, cb8_7, cb8_8, cb8_9, cb8_10, cb8_11, cb8_12, cb8_13, cb8_14, cb8_15, cb8_16, cb8_17, cb8_18, cb8_19, cb8_20, cb8_21, cb8_22, cb8_23, cb8_24, cb8_25, cb8_26, cb8_27, cb8_28, cb8_29, cb8_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_0 : checkRows chart32 group 8 (lookup 8) b9_0 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_8 : checkRows chart32 group 8 (lookup 8) b9_8 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_14 : checkRows chart32 group 8 (lookup 8) b9_14 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_16 : checkRows chart32 group 8 (lookup 8) b9_16 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_19 : checkRows chart32 group 8 (lookup 8) b9_19 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_22 : checkRows chart32 group 8 (lookup 8) b9_22 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_26 : checkRows chart32 group 8 (lookup 8) b9_26 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_28 : checkRows chart32 group 8 (lookup 8) b9_28 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb9_30 : checkRows chart32 group 8 (lookup 8) b9_30 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level9 : checkRows chart32 group 8 (lookup 8) (tiers 9) = true := by
  simp only [tiers, buckets, bucketTier9, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb9_0, cb9_8, cb9_14, cb9_16, cb9_19, cb9_22, cb9_26, cb9_28, cb9_30]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma cb10_9 : checkRows chart32 group 9 (lookup 9) b10_9 = true := by decide +kernel
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma level10 : checkRows chart32 group 9 (lookup 9) (tiers 10) = true := by
  simp only [tiers, buckets, bucketTier10, checkFlatten, checkEmpty, List.all_cons, List.all_nil,
    Bool.and_self, Bool.true_and, cb10_9]
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified0 : verified tiers 0 := verificationStart rfl
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified1 : verified tiers 1 := verificationStep chart_valid32 group_valid
  (lookup_sound 0) verified0 level1
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified2 : verified tiers 2 := verificationStep chart_valid32 group_valid
  (lookup_sound 1) verified1 level2
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified3 : verified tiers 3 := verificationStep chart_valid32 group_valid
  (lookup_sound 2) verified2 level3
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified4 : verified tiers 4 := verificationStep chart_valid32 group_valid
  (lookup_sound 3) verified3 level4
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified5 : verified tiers 5 := verificationStep chart_valid32 group_valid
  (lookup_sound 4) verified4 level5
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified6 : verified tiers 6 := verificationStep chart_valid32 group_valid
  (lookup_sound 5) verified5 level6
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified7 : verified tiers 7 := verificationStep chart_valid32 group_valid
  (lookup_sound 6) verified6 level7
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified8 : verified tiers 8 := verificationStep chart_valid32 group_valid
  (lookup_sound 7) verified7 level8
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified9 : verified tiers 9 := verificationStep chart_valid32 group_valid
  (lookup_sound 8) verified8 level9
set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma verified10 : verified tiers 10 := verificationStep chart_valid32 group_valid
  (lookup_sound 9) verified9 level10

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma noMinor {m : Nat} (cap : m ≤ 10) : ¬ BL m (minorRaw (5 : Fin 7)).toFinset := by
  intro live
  exact verified10 _ sortedStart ((sort_perm _).nodup_iff.mpr startND) m cap
    ((sort_set _).symm ▸ live)
end Minor5

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma allMinor (i : Fin 7) (m : Nat) (cap : m ≤ 10) : ¬ BL m (minorRaw i).toFinset := by
  rw [representative_eq i]
  unfold representative
  split
  · exact Minor1.noMinor cap
  split
  · exact Minor5.noMinor cap
  · exact Minor0.noMinor cap

end Cert10614
end PEqualNP.Outside.L_meta_10614
namespace PEqualNP.Outside.L_meta_10614

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868 FreeSearch1868 Check2516

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 2]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 9]⟩,
    ⟨.or, [7, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [5, 6]⟩,
    ⟨.and, [13, 14]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

lemma witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

lemma witness_size : witness.size = 14 := rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma witness_eval : ∀ x : Fin 7 → Bool, witness.eval (List.ofFn x) = edge x := by
  decide +kernel

def flatEdges : List ℕ :=
  [0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6]

def tableEdge (x : Fin 7 → Bool) : Bool := decide (∃ i < flatEdges.length / 2,
  (List.ofFn x).getD (flatEdges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (flatEdges.getD (2*i+1) 0) false = true)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma table_match : ∀ x, tableEdge x = edge x := by decide +kernel

lemma replacement
    (excluded : ∀ (i : Fin 7) (l : ℕ), l ≤ 10 → ¬ BL l (minorRaw i).toFinset)
    (gates : List Gate) (o : ℕ) (legal : FanInTwo (⟨gates,o⟩ : Circuit))
    (spec : ∀ x, (⟨gates,o⟩ : Circuit).eval (List.ofFn x) = tableEdge x) :
    ∃ (gs' : List Gate) (o' : ℕ),
      (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gates.length ∧
      ∀ x, (⟨gs',o'⟩ : Circuit).eval (List.ofFn x) = tableEdge x := by
  by_cases hasNot : ∃ g ∈ gates, g.op = .not
  · have lower := conditional_binary_lower excluded ⟨gates,o⟩ legal
      (fun x => (spec x).trans (table_match x))
    change 13 ≤ gates.countP costly at lower
    obtain ⟨g,hg,neg⟩ := hasNot
    have strict : gates.countP costly < gates.length :=
      List.countP_lt_length_iff.mpr ⟨g,hg,by simp [costly,neg]⟩
    refine ⟨witness.gates,witness.output,witness_mono,?_,?_⟩
    · change witness.size ≤ gates.length
      rw [witness_size]
      omega
    · intro x
      exact (witness_eval x).trans (table_match x).symm
  · refine ⟨gates,o,?_,le_rfl,spec⟩
    intro g hg
    obtain ⟨op,bound⟩ := legal g hg
    refine ⟨?_,bound⟩
    rcases (show g.op = .and ∨ g.op = .or ∨ g.op = .not from op) with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (hasNot ⟨g,hg,c⟩).elim

end PEqualNP.Outside.L_meta_10614

namespace PEqualNP.Outside.L_meta_10614

open Basis1868 Free1868 FreeSearch1868

theorem exact_statement_from_minors
    (excluded : ∀ (i : Fin 7) (l : ℕ), l ≤ 10 → ¬ BL l (minorRaw i).toFinset) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ spec
  exact replacement excluded gates o (fun g hg => legal g hg) spec

end PEqualNP.Outside.L_meta_10614

theorem PEqualNP.Outside.L_meta_10614 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact PEqualNP.Outside.L_meta_10614.exact_statement_from_minors
    PEqualNP.Outside.L_meta_10614.Cert10614.allMinor
