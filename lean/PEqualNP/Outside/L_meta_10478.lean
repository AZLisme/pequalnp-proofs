import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10478
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
  cases u <;> simp [PEqualNP.Outside.L_meta_10478.Free1868.flip,neg2]
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
  if signed then PEqualNP.Outside.L_meta_10478.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
end WProof1868

namespace WProof1868
open Basis1868 LinearWide1868 Linear1868
open PEqualNP.Outside.L_meta_10478.Board1868 (mult)
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
open PEqualNP.Outside.L_meta_10478.Board1868 (mult)
open PEqualNP.Outside.L_meta_10478.ColorSearch1868 (paint paint_ok)

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
end PEqualNP.Outside.L_meta_10478
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_10478
def edge (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 6) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 4) || (x 2 && x 5) || (x 2 && x 6) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
end PEqualNP.Outside.L_meta_10478
namespace PEqualNP.Outside.L_meta_10478
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
open Projection8403 PEqualNP.Outside.L_meta_10478
namespace Exact8403
def raw8 : List Sig := [(0x2c7070416383820b, 0xa202880a202880a), (0x504cd08a82668454, 0x2c00b002c00b002c), (0x878591143c2c88a1, 0xb002c00b002c00b0), (0x19238220c91c1106, 0xc00b002c00b002c0), (0xe20b240710592038, 0x4c013004c01300), (0x2926838149341c0, 0x7001c007001c00), (0x1fc0fc00fe07e00, 0x80020008002000)]
def pos8 : Array Nat := #[5, 9, 10, 17, 18, 20, 34, 36, 40, 65, 66, 68, 72, 80, 96, 7, 49, 35, 14, 28, 56, 70, 82, 97, 73, 67, 100, 76, 52]
def neg8 : Array Nat := #[0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 33, 48, 64]
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
  obtain ⟨b,hb,sep⟩:=PEqualNP.Outside.L_meta_10478.Conflict1868.pair_sep h p n
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
    (hc : f (top ^^^ mask) &&& mask = 0) (bx : PEqualNP.Outside.L_meta_10478.WProof1868.Sub x top)
    (hit : (f x).testBit i=true) : ∃j,x.testBit j=true ∧ mask.testBit j=true := by
  by_contra! hn
  have sub : PEqualNP.Outside.L_meta_10478.WProof1868.Sub x (top ^^^ mask) := by
    intro j hj; simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hh:=PEqualNP.Outside.L_meta_10478.WProof1868.linMono lin sub i hit
  have bad:=congrArg (fun z : Nat=>z.testBit i) hc
  simp [Nat.testBit_and,hh,hm] at bad

theorem pbit {c : Chart} (h : good c) {a : Nat} (va : Valid1 a) (i : Fin (area c)) :
    (sweep c.spreadP a).testBit i.val = a.testBit (positive c i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10478.WProof1868.validBound va)]
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
  rw [images (linSweep _) (PEqualNP.Outside.L_meta_10478.WProof1868.validBound va)]
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
open PEqualNP.Outside.L_meta_10478.WProof1868 (DS U M multiOne multiTwo Sub)
open PEqualNP.Outside.L_meta_10478.Board1868 (mult)
open PEqualNP.Outside.L_meta_10478.ColorSearch1868 (paint paint_ok)
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
      exact ⟨p,q,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10478.Conflict1868.Unique] using x,by simpa [DS,M,U,Mark,PEqualNP.Outside.L_meta_10478.Conflict1868.Unique] using y⟩
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
  | 0 => #[2, 18, 4, 5, 19, 6, 7, 8, 20, 10, 11, 21, 12, 13, 22, 14]
  | 1 => #[3, 16, 1, 8, 20, 0, 7, 5, 19, 9, 14, 23, 13, 12, 24, 11]
  | 2 => #[6, 17, 4, 3, 16, 2, 1, 8, 20, 10, 9, 25, 14, 13, 22, 12]
  | 3 => #[0, 15, 7, 6, 17, 5, 4, 3, 16, 11, 10, 21, 9, 14, 26, 13]
  | 4 => #[2, 18, 1, 0, 15, 8, 7, 6, 17, 12, 11, 27, 10, 9, 24, 14]
  | 5 => #[0, 15, 1, 2, 18, 3, 4, 5, 19, 9, 10, 25, 11, 12, 24, 13]
  | _ => #[0, 15, 1, 2, 18, 3, 4, 5, 19, 6, 17, 7, 8, 16, 28, 20]
def nCut (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[0, 2, 4, 5, 6, 7, 8, 9, 10, 12, 13]
  | 1 => #[0, 1, 10, 11, 8, 12, 6, 9, 4, 7, 13]
  | 2 => #[0, 2, 1, 3, 10, 11, 8, 12, 6, 9, 13]
  | 3 => #[0, 4, 2, 5, 1, 3, 10, 11, 8, 12, 13]
  | 4 => #[0, 6, 4, 7, 2, 5, 1, 3, 10, 11, 13]
  | 5 => #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13]
  | _ => #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def minorRaw (i : Fin 7) : List Sig :=
  match i.val with
  | 0 => [(0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5), (0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c), (0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f), (0x611c611c611c611c, 0x602c0580b01602c0), (0x81e081e081e081e0, 0x80300600c0180300), (0xfe00fe00fe00fe00, 0x40080100200400)]
  | 1 => [(0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5), (0x81e081e081e081e0, 0x80300600c0180300), (0x611c611c611c611c, 0x602c0580b01602c0), (0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f), (0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c), (0xfe00fe00fe00fe00, 0x40080100200400)]
  | 2 => [(0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c), (0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5), (0x81e081e081e081e0, 0x80300600c0180300), (0x611c611c611c611c, 0x602c0580b01602c0), (0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f), (0xfe00fe00fe00fe00, 0x40080100200400)]
  | 3 => [(0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f), (0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c), (0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5), (0x81e081e081e081e0, 0x80300600c0180300), (0x611c611c611c611c, 0x602c0580b01602c0), (0xfe00fe00fe00fe00, 0x40080100200400)]
  | 4 => [(0x611c611c611c611c, 0x602c0580b01602c0), (0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f), (0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c), (0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5), (0x81e081e081e081e0, 0x80300600c0180300), (0xfe00fe00fe00fe00, 0x40080100200400)]
  | 5 => [(0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5), (0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c), (0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f), (0x611c611c611c611c, 0x602c0580b01602c0), (0x81e081e081e081e0, 0x80300600c0180300), (0xfe00fe00fe00fe00, 0x40080100200400)]
  | _ => [(0xdbd8dbd8dbd8dbd8, 0x7f5bfadfd6feb7f5), (0x65a065a065a065a, 0x2c01600b005802c), (0xb66cb66cb66cb66c, 0xf4ffa7fd3fe9ff4f), (0x911c911c911c911c, 0x2c01600b005802c0), (0xe1e0e1e0e1e0e1e0, 0x3009804c02601300), (0xfe00fe00fe00fe00, 0xc00e007003801c00)]
def cutPairs (i : Fin 7) : List (Nat × Nat) :=
  match i.val with
  | 0 => [(0, 4), (3, 6), (0, 1), (2, 1), (5, 1), (9, 1)]
  | 1 => [(0, 4), (5, 1), (2, 1), (0, 1), (3, 6), (9, 1)]
  | 2 => [(3, 6), (0, 4), (5, 1), (2, 1), (0, 1), (9, 1)]
  | 3 => [(0, 1), (3, 6), (0, 4), (5, 1), (2, 1), (9, 1)]
  | 4 => [(2, 1), (0, 1), (3, 6), (0, 4), (5, 1), (9, 1)]
  | 5 => [(0, 4), (3, 6), (0, 1), (2, 1), (5, 1), (9, 1)]
  | _ => [(0, 4), (3, 6), (0, 1), (2, 1), (5, 1), (9, 2)]
def pPairs (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[0, 0, 0, 15, 1, 0, 0, 1, 0, 3, 0, 16, 0, 9]
  | 1 => #[2, 17, 0, 0, 2, 18, 4, 2, 2, 4, 2, 6, 2, 10]
  | 2 => #[5, 0, 0, 15, 0, 0, 0, 19, 0, 5, 0, 7, 0, 11]
  | 3 => #[2, 1, 1, 2, 1, 18, 0, 0, 1, 20, 1, 8, 1, 12]
  | 4 => #[4, 3, 3, 4, 3, 5, 3, 19, 0, 0, 3, 16, 3, 13]
  | 5 => #[6, 17, 7, 6, 6, 7, 6, 8, 6, 20, 0, 0, 6, 14]
  | _ => #[10, 9, 9, 10, 9, 11, 9, 12, 9, 13, 9, 14, 0, 0]
def nPairs (i : Fin 7) : Array Nat :=
  match i.val with
  | 0 => #[0, 0, 4, 5, 6, 4, 4, 6, 4, 8, 4, 12, 4, 13]
  | 1 => #[6, 11, 0, 0, 6, 7, 8, 6, 6, 8, 6, 10, 6, 13]
  | 2 => #[8, 1, 1, 3, 0, 0, 1, 9, 1, 8, 1, 10, 1, 13]
  | 3 => #[2, 1, 1, 2, 1, 5, 0, 0, 1, 12, 1, 10, 1, 13]
  | 4 => #[2, 1, 1, 2, 1, 4, 1, 7, 0, 0, 1, 11, 1, 13]
  | 5 => #[2, 3, 4, 2, 2, 4, 2, 6, 2, 9, 0, 0, 2, 13]
  | _ => #[2, 1, 1, 2, 1, 4, 1, 6, 1, 8, 1, 10, 0, 0]

def cut (i : Fin 7) : SigHom :=
  pairHom (fun j => Fin.ofNat 64 ((pCut i).getD (j.val % (pCut i).size) 0))
    (fun j => Fin.ofNat 64 ((nCut i).getD (j.val % (nCut i).size) 0))

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma needFull : necessary fullRaw :=
  needFrom (pn := [(0, 4), (2, 6), (0, 1), (1, 1), (3, 1), (6, 2), (9, 1)]) (by decide) (by decide +kernel)

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
    (excluded : ∀ (i : Fin 7) (l : ℕ), l ≤ 9 → ¬ BL l (minorRaw i).toFinset)
    (C : Circuit) (legal : FanInTwo C)
    (spec : ∀ x, C.eval (List.ofFn x) = edge x) : 12 ≤ C.gates.countP costly := by
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
  if i=6 then 6 else 0

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
lemma representative_eq : ∀ i, (minorRaw i).toFinset =
    (minorRaw (representative i)).toFinset := by decide +kernel

end PEqualNP.Outside.L_meta_10478


namespace PEqualNP.Outside.L_meta_10478
open Basis1868 Free1868 FreeSearch1868 Cuts1868 Check2516 Exact8403 Projection8403

def chart : QuickQ.Chart := ⟨16,16,[(false, 0, 0xffff), (true, 120, 0xff000000000000000000000000000000ff), (true, 60, 0xf000000000000000f000000000000000f000000000000000f), (true, 30, 0x300000003000000030000000300000003000000030000000300000003), (true, 15, 0x1000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0x1000100010001000100010001000100010001000100010001000100010001), (true, 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 2, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 8, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)],[(false, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (false, 0, 0xffff), (true, 16, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 32, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 64, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), (true, 128, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chart_valid : QuickQ.good chart := by
  apply QuickQ.goodOfCompact
  unfold QuickQ.compactGood
  decide +kernel

def key (x : Sig) : ℕ := x.1 * 2^64 + x.2

def insertSignal (x : Sig) : List Sig → List Sig
  | [] => [x]
  | a::as => if key x ≤ key a then x::a::as else a::insertSignal x as

def sortSignals : List Sig → List Sig
  | [] => []
  | a::as => insertSignal a (sortSignals as)

lemma insert_perm (a : Sig) (w : List Sig) : (insertSignal a w).Perm (a::w) := by
  induction w with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : key a ≤ key b
    · simp [insertSignal,h]
    · simpa [insertSignal,h] using (List.Perm.cons b ih).trans (.swap a b bs)

lemma sorted_perm (v : List Sig) : (sortSignals v).Perm v := by
  induction v with
  | nil => exact .refl _
  | cons a bs ih => exact (insert_perm a (sortSignals bs)).trans (.cons a ih)

lemma sorted_set (v : List Sig) : (sortSignals v).toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (sorted_perm v).mem_iff (a:=a)

lemma live_card {n : ℕ} {S : Finset Sig} (live : BL n S) : S.card ≤ n+1 := by
  induction live with
  | stop => simp
  | @step k U a b d s t ha hb ac bc ab fresh tail ih =>
    have new : blend d s t a b ∉ U := fun h =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem new] at ih
    have ca := Finset.card_insert_le (s:=insert b U) (a:=a)
    have cb := Finset.card_insert_le (s:=U) (a:=b)
    omega

def absent (n : ℕ) (lookup : List Sig → Bool) (w : List Sig) : Bool :=
  (w.length ≤ n+1) && QuickQ.test chart true (n+2-w.length) w &&
    !(lookup (sortSignals w))

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
  let g:=PEqualNP.Outside.L_meta_10478.Board1868.mult s
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


def rowFast (n : ℕ) (lookup : List Sig → Bool) (v : List Sig) : Bool :=
  let ws := v.map (QuickQ.diff chart true)
  !(baseTest v || scanPairs (GroupQ.fork chart true n
    (fun w => lookup (sortSignals w)) v ws) ws)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rowFast_eq (n : ℕ) (lookup : List Sig → Bool) (v : List Sig) :
    rowFast n lookup v = !(baseTest v || scanPairs (pairB v (absent n lookup)) v) := by
  let ws := v.map (QuickQ.diff chart true)
  let code := fun w => lookup (sortSignals w)
  have localEq : GroupQ.fork chart true n code v ws = PackQ.forkS chart n code ws v := by
    funext a b
    exact GroupQ.forkSEQ chart n code v ws a b
  unfold rowFast
  change (!(baseTest v || scanPairs (GroupQ.fork chart true n code v ws) ws)) = _
  rw [localEq, show ws = v.map (QuickQ.diff chart true) from rfl]
  rw [PackQ.scanMap _ _ _ (PackQ.forkSMap _ _ _ _)]
  rfl

def checkRows (n : ℕ) (lookup : List Sig → Bool) (rs : List (List Sig)) : Bool :=
  rs.all (rowFast n lookup)

lemma checkRows_append (n : ℕ) (lookup : List Sig → Bool) (a b : List (List Sig)) :
    checkRows n lookup (a++b) = (checkRows n lookup a && checkRows n lookup b) :=
  List.all_append

lemma checkRows_flatten (n : ℕ) (lookup : List Sig → Bool) (rows : List (List (List Sig))) :
    checkRows n lookup rows.flatten = rows.all (checkRows n lookup) := by
  induction rows with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatten_cons,List.all_cons,checkRows_append,ih]

lemma checkRows_nil (n : ℕ) (lookup : List Sig → Bool) :
    checkRows n lookup [] = true := rfl

def verified (tiers : ℕ → List (List Sig)) (n : ℕ) : Prop :=
  ∀ v ∈ tiers n, v.Nodup → ∀ k ≤ n, ¬ BL k v.toFinset

lemma verificationStep {tiers : ℕ → List (List Sig)} {lookup : List Sig → Bool} {n : ℕ}
    (lookupSound : ∀ w, lookup w = true → w ∈ tiers n) (before : verified tiers n)
    (check : checkRows n lookup (tiers (n+1)) = true) : verified tiers (n+1) := by
  intro v hv nd k kn live
  have changeStep : ∀ w : List Sig, w.Nodup → ∀ l ≤ n, BL l w.toFinset → absent n lookup w = true := by
    intro w wn l ln run
    have cn := live_card run
    rw [List.toFinset_card_of_nodup wn] at cn
    have len : w.length ≤ n+1 := by omega
    have certified := QuickQ.testSigned chart_valid ln wn run
    have miss : lookup (sortSignals w) = false := by
      cases h : lookup (sortSignals w)
      · rfl
      · exact (before _ (lookupSound _ h) ((sorted_perm w).nodup_iff.mpr wn)
          l ln ((sorted_set w).symm ▸ run)).elim
    simp [absent,len,certified,miss]
  have possible := oneStep live n kn v nd rfl (absent n lookup) changeStep
  have ruled := List.all_eq_true.mp check v hv
  simp [rowFast_eq,possible] at ruled


def hashBucket (w : List Sig) : Nat :=
  (w.foldl (fun s a => s + a.1 * 31 + a.2 * 11) 0) % 17

def bucketHas (w : List Sig) : List (List (List Sig)) → Nat → Bool
  | [], _ => false
  | a::_, 0 => a.contains w
  | _::as, i+1 => bucketHas w as i

lemma bucketHas_sound (w : List Sig) (ls : List (List (List Sig))) (idx : Nat)
    (h : bucketHas w ls idx = true) : w ∈ ls.flatten := by
  induction ls generalizing idx with
  | nil => simp [bucketHas] at h
  | cons a as ih =>
    cases idx with
    | zero =>
      have q : w ∈ a := by simpa [bucketHas] using h
      simp [q]
    | succ i =>
      have q : w ∈ as.flatten := ih i (by simpa [bucketHas] using h)
      simp [q]

namespace Minor0

def w0 : Sig := (0x24002400240024, 0xa1b43686d0da1b43)
def w1 : Sig := (0x60006000600060, 0x8790f21e43c8790f)
def w2 : Sig := (0x6c006c006c006c, 0xa7b4f69ed3da7b4f)
def w3 : Sig := (0x7e007e007e007e, 0xb7b6f6dedbdb7b6f)
def w4 : Sig := (0x17c017c017c017c, 0xe7bcf79ef3de7bcf)
def w5 : Sig := (0x180018001800180, 0x0)
def w6 : Sig := (0x180018001800180, 0xe8bd17a2f45e8bd1)
def w7 : Sig := (0x1d801d801d801d8, 0xfabf57eafd5fabf5)
def w8 : Sig := (0x1da01da01da01da, 0xfebfd7faff5febfd)
def w9 : Sig := (0x1dc01dc01dc01dc, 0xfabf57eafd5fabf5)
def w10 : Sig := (0x1e001e001e001e0, 0x80300600c0180300)
def w11 : Sig := (0x1ec01ec01ec01ec, 0xa7b4f69ed3da7b4f)
def w12 : Sig := (0x1f801f801f801f8, 0xfabf57eafd5fabf5)
def w13 : Sig := (0x1fc01fc01fc01fc, 0xffbff7feffdffbff)
def w14 : Sig := (0x458045804580458, 0x1202404809012024)
def w15 : Sig := (0x5d805d805d805d8, 0xfabf57eafd5fabf5)
def w16 : Sig := (0xc5a0c5a0c5a0c5a, 0x1602c0580b01602c)
def w17 : Sig := (0xc6c0c6c0c6c0c6c, 0xa7b4f69ed3da7b4f)
def w18 : Sig := (0xc7e0c7e0c7e0c7e, 0xb7b6f6dedbdb7b6f)
def w19 : Sig := (0xdda0dda0dda0dda, 0x1602c0580b01602c)
def w20 : Sig := (0xdda0dda0dda0dda, 0xfebfd7faff5febfd)
def w21 : Sig := (0xe000e000e000e00, 0x7c0f81f03e07c0f)
def w22 : Sig := (0x1000100010001000, 0x0)
def w23 : Sig := (0x1190119011901190, 0x580b01602c0580b0)
def w24 : Sig := (0x11d811d811d811d8, 0xfabf57eafd5fabf5)
def w25 : Sig := (0x1400140014001400, 0x1ac3586b0d61ac35)
def w26 : Sig := (0x1c5a1c5a1c5a1c5a, 0x1602c0580b01602c)
def w27 : Sig := (0x1e001e001e001e00, 0x40080100200400)
def w28 : Sig := (0x21d821d821d821d8, 0xfabf57eafd5fabf5)
def w29 : Sig := (0x3000300030003000, 0x68cd19a334668cd1)
def w30 : Sig := (0x3418341834183418, 0x7acf59eb3d67acf5)
def w31 : Sig := (0x35d835d835d835d8, 0xfaff5febfd7faff5)
def w32 : Sig := (0x4a004a004a004a00, 0x0)
def w33 : Sig := (0x4a244a244a244a24, 0x500a0140280500a)
def w34 : Sig := (0x4a6c4a6c4a6c4a6c, 0xa7b4f69ed3da7b4f)
def w35 : Sig := (0x4e5a4e5a4e5a4e5a, 0x1602c0580b01602c)
def w36 : Sig := (0x4e7e4e7e4e7e4e7e, 0x1702e05c0b81702e)
def w37 : Sig := (0x601c601c601c601c, 0x600c0180300600c0)
def w38 : Sig := (0x606c606c606c606c, 0xa7b4f69ed3da7b4f)
def w39 : Sig := (0x611c611c611c611c, 0x602c0580b01602c0)
def w40 : Sig := (0x617c617c617c617c, 0xe7bcf79ef3de7bcf)
def w41 : Sig := (0x61dc61dc61dc61dc, 0xfabf57eafd5fabf5)
def w42 : Sig := (0x61fc61fc61fc61fc, 0xe03c0780f01e03c0)
def w43 : Sig := (0x6b1c6b1c6b1c6b1c, 0x602c0580b01602c0)
def w44 : Sig := (0x6e0c6e0c6e0c6e0c, 0x27c4f89f13e27c4f)
def w45 : Sig := (0x6e6c6e6c6e6c6e6c, 0xa7f4fe9fd3fa7f4f)
def w46 : Sig := (0x711c711c711c711c, 0x602c0580b01602c0)
def w47 : Sig := (0x7e007e007e007e00, 0x40080100200400)
def w48 : Sig := (0x7e1c7e1c7e1c7e1c, 0x7fcff9ff3fe7fcff)
def w49 : Sig := (0x8000800080008000, 0x0)
def w50 : Sig := (0x8060806080608060, 0x80300600c0180300)
def w51 : Sig := (0x806c806c806c806c, 0xa7b4f69ed3da7b4f)
def w52 : Sig := (0x80e080e080e080e0, 0x8010020040080100)
def w53 : Sig := (0x81a081a081a081a0, 0x80300600c0180300)
def w54 : Sig := (0x81c081c081c081c0, 0x80300600c0180300)
def w55 : Sig := (0x81d881d881d881d8, 0xfabf57eafd5fabf5)
def w56 : Sig := (0x81e081e081e081e0, 0x80300600c0180300)
def w57 : Sig := (0x81ec81ec81ec81ec, 0xa7b4f69ed3da7b4f)
def w58 : Sig := (0x81f881f881f881f8, 0xfabf57eafd5fabf5)
def w59 : Sig := (0x8c5a8c5a8c5a8c5a, 0x1602c0580b01602c)
def w60 : Sig := (0x8dfa8dfa8dfa8dfa, 0x9632c658cb19632c)
def w61 : Sig := (0x8e608e608e608e60, 0x87d0fa1f43e87d0f)
def w62 : Sig := (0x8e628e628e628e62, 0x97d2fa5f4be97d2f)
def w63 : Sig := (0x91e091e091e091e0, 0x80300600c0180300)
def w64 : Sig := (0x94c094c094c094c0, 0x9ad35a6b4d69ad35)
def w65 : Sig := (0x9e009e009e009e00, 0x40080100200400)
def w66 : Sig := (0x9ee09ee09ee09ee0, 0x80500a0140280500)
def w67 : Sig := (0x9ee09ee09ee09ee0, 0x9fd3fa7f4fe9fd3f)
def w68 : Sig := (0x9fe09fe09fe09fe0, 0x80700e01c0380700)
def w69 : Sig := (0xa000a000a000a000, 0xa0f41e83d07a0f41)
def w70 : Sig := (0xa1d8a1d8a1d8a1d8, 0xfabf57eafd5fabf5)
def w71 : Sig := (0xa448a448a448a448, 0xa2f45e8bd17a2f45)
def w72 : Sig := (0xa46ca46ca46ca46c, 0xa7f4fe9fd3fa7f4f)
def w73 : Sig := (0xa5d8a5d8a5d8a5d8, 0xfaff5febfd7faff5)
def w74 : Sig := (0xb000b000b000b000, 0x40080100200400)
def w75 : Sig := (0xb180b180b180b180, 0xe8fd1fa3f47e8fd1)
def w76 : Sig := (0xb1a0b1a0b1a0b1a0, 0xe8fd1fa3f47e8fd1)
def w77 : Sig := (0xb1e0b1e0b1e0b1e0, 0x80700e01c0380700)
def w78 : Sig := (0xb400b400b400b400, 0x40080100200400)
def w79 : Sig := (0xb458b458b458b458, 0xfaff5febfd7faff5)
def w80 : Sig := (0xb590b590b590b590, 0x584b09612c2584b0)
def w81 : Sig := (0xb5c0b5c0b5c0b5c0, 0x80700e01c0380700)
def w82 : Sig := (0xb5d8b5d8b5d8b5d8, 0xfaff5febfd7faff5)
def w83 : Sig := (0xb5e0b5e0b5e0b5e0, 0x80700e01c0380700)
def w84 : Sig := (0xb5f8b5f8b5f8b5f8, 0xfaff5febfd7faff5)
def w85 : Sig := (0xbddabddabddabdda, 0xfeffdffbff7feffd)
def w86 : Sig := (0xcbe0cbe0cbe0cbe0, 0x80300600c0180300)
def w87 : Sig := (0xe11ce11ce11ce11c, 0x602c0580b01602c0)
def w88 : Sig := (0xe17ce17ce17ce17c, 0xe03c0780f01e03c0)
def w89 : Sig := (0xe1bce1bce1bce1bc, 0xe03c0780f01e03c0)
def w90 : Sig := (0xe1dce1dce1dce1dc, 0xe03c0780f01e03c0)
def w91 : Sig := (0xe1fce1fce1fce1fc, 0xe03c0780f01e03c0)
def w92 : Sig := (0xe224e224e224e224, 0xa1f43e87d0fa1f43)
def w93 : Sig := (0xe324e324e324e324, 0xe1fc3f87f0fe1fc3)
def w94 : Sig := (0xee00ee00ee00ee00, 0x40080100200400)
def w95 : Sig := (0xee24ee24ee24ee24, 0x540a81502a0540a)
def w96 : Sig := (0xee60ee60ee60ee60, 0x80700e01c0380700)
def w97 : Sig := (0xee6cee6cee6cee6c, 0xa7f4fe9fd3fa7f4f)
def w98 : Sig := (0xee7eee7eee7eee7e, 0xb7f6fedfdbfb7f6f)
def w99 : Sig := (0xef7cef7cef7cef7c, 0xe7fcff9ff3fe7fcf)
def w100 : Sig := (0xefe0efe0efe0efe0, 0x80700e01c0380700)
def w101 : Sig := (0xefecefecefecefec, 0xa7f4fe9fd3fa7f4f)
def w102 : Sig := (0xf184f184f184f184, 0xe8fd1fa3f47e8fd1)
def w103 : Sig := (0xf200f200f200f200, 0x40080100200400)
def w104 : Sig := (0xf380f380f380f380, 0xe8fd1fa3f47e8fd1)
def w105 : Sig := (0xf3a0f3a0f3a0f3a0, 0x80700e01c0380700)
def w106 : Sig := (0xf3e0f3e0f3e0f3e0, 0x80700e01c0380700)
def w107 : Sig := (0xf5dcf5dcf5dcf5dc, 0xfaff5febfd7faff5)
def w108 : Sig := (0xfe00fe00fe00fe00, 0x40080100200400)
def w109 : Sig := (0xfe24fe24fe24fe24, 0x540a81502a0540a)
def w110 : Sig := (0xfe5afe5afe5afe5a, 0x1642c8590b21642c)
def w111 : Sig := (0xfe60fe60fe60fe60, 0x80700e01c0380700)
def w112 : Sig := (0xfe6cfe6cfe6cfe6c, 0xa7f4fe9fd3fa7f4f)
def w113 : Sig := (0xfee0fee0fee0fee0, 0x80500a0140280500)
def w114 : Sig := (0xff1cff1cff1cff1c, 0x606c0d81b03606c0)
def w115 : Sig := (0xff80ff80ff80ff80, 0x40080100200400)
def w116 : Sig := (0xff90ff90ff90ff90, 0x584b09612c2584b0)
def w117 : Sig := (0xffa0ffa0ffa0ffa0, 0x80700e01c0380700)
def w118 : Sig := (0xffc0ffc0ffc0ffc0, 0x80700e01c0380700)
def w119 : Sig := (0xffd8ffd8ffd8ffd8, 0xfaff5febfd7faff5)
def w120 : Sig := (0xffe0ffe0ffe0ffe0, 0x80700e01c0380700)
def w121 : Sig := (0xfffcfffcfffcfffc, 0xe07c0f81f03e07c0)
def w122 : Sig := (0xfffcfffcfffcfffc, 0xffffffffffffffff)
def tier1 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier2 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier3 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier4 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def b5_0 : List (List Sig) := [[w16, w28, w30, w39, w97, w120],
  [w25, w75, w91, w97, w108, w120]]
def b5_1 : List (List Sig) := [[w6, w30, w75, w91, w97, w108]]
def b5_2 : List (List Sig) := [[w2, w6, w23, w39, w56, w75],
  [w30, w65, w75, w91, w97, w108]]
def b5_3 : List (List Sig) := [[w2, w16, w21, w82, w91, w120],
  [w2, w16, w82, w91, w101, w121],
  [w6, w39, w56, w75, w97, w116],
  [w11, w16, w82, w91, w97, w121]]
def b5_5 : List (List Sig) := [[w6, w29, w39, w82, w97, w120]]
def b5_6 : List (List Sig) := [[w7, w16, w30, w39, w68, w97]]
def b5_7 : List (List Sig) := [[w30, w74, w75, w91, w97, w108]]
def b5_8 : List (List Sig) := [[w27, w30, w75, w91, w97, w108]]
def b5_10 : List (List Sig) := [[w2, w7, w16, w39, w56, w69],
  [w7, w16, w25, w56, w97, w121],
  [w7, w56, w65, w75, w91, w97]]
def b5_12 : List (List Sig) := [[w7, w29, w75, w91, w97, w108]]
def b5_13 : List (List Sig) := [[w2, w7, w39, w56, w69, w75],
  [w15, w16, w30, w39, w97, w120],
  [w30, w75, w91, w97, w108, w121]]
def b5_14 : List (List Sig) := [[w30, w75, w91, w97, w103, w108]]
def b5_16 : List (List Sig) := [[w2, w16, w21, w39, w82, w120]]
def tier5 : List (List (List Sig)) := [b5_0, b5_1, b5_2, b5_3, [], b5_5, b5_6, b5_7, b5_8, [], b5_10, [], b5_12, b5_13, b5_14, [], b5_16]
def b6_0 : List (List Sig) := [[w2, w16, w39, w56, w71, w82, w110],
  [w7, w16, w30, w39, w56, w65, w97],
  [w7, w16, w39, w60, w82, w97, w120],
  [w7, w39, w56, w76, w97, w108],
  [w12, w39, w56, w75, w97, w108],
  [w13, w39, w56, w75, w97],
  [w16, w27, w30, w82, w91, w97, w108],
  [w16, w29, w82, w91, w97, w108],
  [w16, w82, w91, w94, w97, w120],
  [w16, w82, w91, w97, w100, w108],
  [w16, w82, w91, w97, w108, w115],
  [w28, w39, w56, w75, w97, w108],
  [w39, w41, w56, w75, w97, w108],
  [w39, w56, w74, w75, w82, w97, w120],
  [w39, w56, w75, w77, w82, w97, w108],
  [w56, w64, w75, w97, w108, w114],
  [w56, w75, w82, w91, w97, w103, w108]]
def b6_1 : List (List Sig) := [[w7, w16, w30, w39, w56, w97, w114],
  [w16, w30, w39, w65, w82, w97, w120],
  [w16, w30, w39, w68, w82, w97, w108],
  [w16, w82, w88, w97, w108, w120],
  [w56, w75, w82, w91, w97, w108, w110],
  [w60, w82, w91, w97, w108, w110]]
def b6_2 : List (List Sig) := [[w6, w30, w39, w56, w75, w97, w108],
  [w7, w16, w56, w65, w82, w91, w97],
  [w7, w39, w56, w60, w75, w97, w108],
  [w14, w82, w91, w97, w108, w120],
  [w16, w21, w56, w82, w97, w108, w114],
  [w16, w30, w39, w82, w97, w114, w120],
  [w16, w39, w40, w56, w82, w97, w120],
  [w30, w75, w91, w97, w108]]
def b6_3 : List (List Sig) := [[w7, w16, w30, w91, w97, w108],
  [w7, w16, w56, w82, w91, w97, w114],
  [w16, w28, w39, w56, w82, w97, w120],
  [w16, w30, w75, w91, w97, w108],
  [w16, w56, w64, w82, w97, w114, w120],
  [w16, w82, w91, w97, w103, w120],
  [w16, w82, w91, w97, w106, w108],
  [w25, w39, w56, w75, w97, w108],
  [w29, w75, w82, w91, w97, w108],
  [w30, w39, w56, w65, w75, w97, w108],
  [w30, w39, w75, w91, w97, w108],
  [w39, w60, w75, w82, w97, w108, w120]]
def b6_4 : List (List Sig) := [[w6, w56, w75, w82, w91, w97, w108],
  [w7, w39, w56, w75, w97, w120],
  [w13, w39, w56, w75, w97, w108],
  [w16, w30, w39, w64, w97, w108, w120],
  [w16, w82, w91, w97, w110, w120],
  [w30, w39, w56, w75, w97, w108, w114],
  [w39, w55, w56, w75, w97, w108],
  [w56, w64, w75, w91, w97, w108]]
def b6_5 : List (List Sig) := [[w2, w16, w39, w56, w69, w82, w108],
  [w2, w16, w39, w56, w82, w97, w121],
  [w7, w16, w56, w64, w91, w97, w108],
  [w16, w25, w56, w82, w97, w108, w121],
  [w16, w30, w82, w91, w97, w108, w121],
  [w16, w82, w90, w97, w108, w120],
  [w16, w82, w91, w97, w108, w118],
  [w24, w39, w56, w75, w97, w108],
  [w56, w65, w75, w82, w91, w97, w108]]
def b6_6 : List (List Sig) := [[w2, w7, w39, w56, w75, w97],
  [w2, w16, w39, w44, w56, w82, w114],
  [w7, w16, w39, w56, w69, w97, w108],
  [w7, w39, w56, w65, w75, w97],
  [w16, w30, w82, w91, w97, w103, w108],
  [w16, w64, w82, w91, w97, w108, w120],
  [w16, w82, w91, w97, w105, w108],
  [w56, w67, w75, w97, w108],
  [w56, w75, w82, w91, w97, w108, w114]]
def b6_7 : List (List Sig) := [[w2, w7, w16, w39, w56, w75, w97],
  [w2, w16, w56, w61, w82, w91, w108],
  [w2, w23, w39, w56, w75, w108],
  [w7, w39, w56, w75, w97, w114],
  [w15, w16, w30, w39, w56, w97, w108],
  [w16, w30, w82, w91, w97, w108, w110],
  [w16, w56, w70, w82, w91, w97, w108],
  [w16, w57, w82, w91, w97, w108],
  [w25, w56, w75, w91, w97, w108],
  [w39, w56, w75, w82, w97, w103, w120],
  [w39, w56, w75, w82, w97, w106, w108]]
def b6_8 : List (List Sig) := [[w2, w16, w82, w91, w97, w120],
  [w2, w39, w56, w69, w75, w82, w108],
  [w7, w16, w25, w56, w91, w97, w108],
  [w7, w16, w27, w56, w82, w91, w97],
  [w7, w16, w30, w39, w60, w97, w108],
  [w16, w39, w44, w82, w97, w114, w120],
  [w16, w68, w82, w91, w97, w108],
  [w30, w39, w56, w74, w75, w97, w108],
  [w39, w56, w75, w82, w97, w110, w120],
  [w39, w56, w75, w97, w108, w116],
  [w39, w60, w82, w97, w110, w120]]
def b6_9 : List (List Sig) := [[w2, w16, w39, w82, w91, w97, w120],
  [w2, w16, w56, w82, w91, w97, w121],
  [w7, w16, w39, w56, w68, w82, w97],
  [w7, w37, w56, w75, w97, w108],
  [w7, w39, w56, w69, w75, w97, w108],
  [w15, w16, w56, w82, w91, w97, w108],
  [w16, w25, w82, w91, w97, w108, w120],
  [w16, w81, w82, w91, w97, w108],
  [w39, w56, w69, w82, w97, w108, w110],
  [w60, w75, w82, w91, w97, w108]]
def b6_10 : List (List Sig) := [[w2, w6, w16, w39, w56, w82, w97],
  [w2, w16, w21, w39, w56, w82, w108],
  [w2, w39, w56, w75, w82, w97, w110],
  [w7, w16, w30, w39, w97, w120],
  [w7, w16, w60, w82, w91, w97, w108],
  [w7, w39, w56, w75, w97, w108],
  [w7, w39, w56, w97, w102, w108],
  [w56, w74, w75, w82, w91, w97, w108]]
def b6_11 : List (List Sig) := [[w6, w39, w56, w75, w82, w97, w120],
  [w16, w28, w30, w39, w56, w97, w108],
  [w16, w30, w56, w64, w97, w108, w114],
  [w16, w30, w65, w82, w91, w97, w108],
  [w27, w56, w75, w82, w91, w97, w108],
  [w30, w39, w60, w82, w97, w108, w110],
  [w39, w56, w58, w75, w97, w108]]
def b6_12 : List (List Sig) := [[w2, w7, w16, w39, w56, w82, w92],
  [w6, w39, w56, w69, w82, w97, w108],
  [w7, w16, w39, w56, w64, w97, w120],
  [w7, w16, w82, w91, w97, w120],
  [w16, w21, w39, w82, w97, w108, w120],
  [w16, w21, w56, w82, w97, w108, w121],
  [w16, w30, w82, w91, w97, w108, w114],
  [w16, w40, w56, w82, w91, w97, w108],
  [w16, w82, w91, w97, w108, w120],
  [w39, w56, w65, w75, w82, w97, w120],
  [w39, w56, w68, w75, w82, w97, w108],
  [w39, w56, w75, w80, w97, w108]]
def b6_13 : List (List Sig) := [[w2, w6, w39, w56, w75, w82, w97],
  [w2, w7, w16, w39, w56, w71],
  [w2, w16, w82, w91, w101, w108],
  [w7, w16, w56, w82, w91, w97, w121],
  [w7, w29, w39, w56, w75, w97, w108],
  [w9, w39, w56, w75, w97, w108],
  [w11, w16, w82, w91, w97, w108],
  [w15, w39, w56, w75, w97, w108],
  [w16, w28, w56, w82, w91, w97, w108],
  [w16, w30, w39, w82, w97, w103, w120],
  [w16, w30, w39, w82, w97, w106, w108],
  [w16, w82, w91, w97, w115],
  [w19, w82, w91, w97, w108],
  [w30, w39, w75, w97, w108, w120],
  [w39, w56, w75, w82, w97, w114, w120]]
def b6_14 : List (List Sig) := [[w2, w16, w21, w56, w82, w91, w108],
  [w2, w16, w39, w56, w61, w82, w120],
  [w7, w16, w56, w64, w97, w114],
  [w7, w36, w39, w56, w97, w108],
  [w7, w56, w75, w91, w97, w108],
  [w16, w30, w39, w82, w97, w110, w120],
  [w29, w39, w75, w82, w97, w108, w120]]
def b6_15 : List (List Sig) := [[w2, w16, w39, w44, w82, w120],
  [w2, w39, w56, w75, w82, w92, w108],
  [w6, w23, w39, w56, w75, w97, w108],
  [w7, w16, w56, w75, w91, w97, w108],
  [w7, w39, w56, w75, w91, w97, w108],
  [w7, w39, w56, w75, w94, w97],
  [w16, w79, w91, w97, w108],
  [w16, w82, w89, w97, w108, w120],
  [w16, w82, w91, w97, w108, w117],
  [w30, w39, w56, w75, w97, w103, w108],
  [w39, w48, w75, w97, w108],
  [w39, w56, w64, w75, w97, w108, w120],
  [w75, w82, w91, w97, w108, w120]]
def b6_16 : List (List Sig) := [[w2, w16, w56, w82, w91, w97, w114],
  [w6, w29, w39, w56, w82, w97, w108],
  [w7, w39, w47, w56, w75, w97],
  [w15, w16, w39, w56, w82, w97, w120],
  [w16, w21, w82, w91, w97, w108, w120],
  [w16, w75, w82, w91, w97, w108, w120],
  [w16, w78, w82, w91, w97, w120],
  [w16, w82, w83, w91, w97, w108],
  [w16, w82, w91, w97, w101, w108, w121],
  [w30, w39, w56, w75, w97, w108, w110],
  [w39, w75, w82, w91, w97, w108, w120],
  [w56, w75, w82, w91, w97, w108, w121]]
def tier6 : List (List (List Sig)) := [b6_0, b6_1, b6_2, b6_3, b6_4, b6_5, b6_6, b6_7, b6_8, b6_9, b6_10, b6_11, b6_12, b6_13, b6_14, b6_15, b6_16]
def b7_0 : List (List Sig) := [[w6, w39, w56, w75, w82, w97, w108],
  [w16, w39, w56, w75, w82, w97, w108, w120],
  [w16, w39, w56, w78, w82, w97, w120],
  [w16, w39, w56, w82, w83, w97, w108],
  [w16, w39, w56, w82, w97, w108, w116],
  [w16, w39, w60, w82, w97, w108, w120],
  [w16, w56, w82, w91, w97, w108, w120],
  [w37, w56, w75, w82, w97, w108],
  [w39, w56, w64, w75, w97, w108],
  [w39, w56, w69, w75, w82, w97, w108]]
def b7_1 : List (List Sig) := [[w2, w39, w56, w75, w82, w97, w108],
  [w7, w16, w37, w56, w82, w97, w108],
  [w7, w16, w39, w56, w64, w97, w108],
  [w16, w29, w39, w56, w82, w97, w108],
  [w16, w39, w56, w82, w94, w97, w120],
  [w16, w39, w56, w82, w95, w97, w108],
  [w16, w39, w56, w82, w97, w100, w108],
  [w16, w39, w56, w82, w97, w108, w115],
  [w39, w56, w65, w75, w82, w97, w108],
  [w39, w56, w75, w82, w97, w108],
  [w39, w56, w75, w97, w107, w108],
  [w39, w56, w82, w97, w102, w108]]
def b7_2 : List (List Sig) := [[w2, w16, w39, w56, w75, w82, w97, w108],
  [w2, w16, w39, w56, w78, w82, w97],
  [w2, w16, w56, w82, w91, w97, w108],
  [w7, w16, w39, w56, w82, w97, w108],
  [w7, w16, w39, w56, w97, w107, w108],
  [w16, w21, w39, w56, w82, w97, w108],
  [w16, w38, w39, w56, w82, w97, w108],
  [w16, w39, w44, w56, w82, w97, w108, w114],
  [w16, w39, w56, w72, w82, w108],
  [w16, w39, w56, w82, w96, w97, w108],
  [w16, w56, w65, w82, w91, w97, w108],
  [w16, w56, w82, w91, w97, w108],
  [w39, w56, w60, w82, w97, w108, w110],
  [w39, w56, w75, w82, w97, w108, w114]]
def b7_3 : List (List Sig) := [[w2, w16, w39, w56, w61, w82, w108],
  [w2, w16, w39, w56, w82, w91, w97, w108],
  [w14, w39, w56, w82, w97, w108, w120],
  [w16, w39, w56, w58, w82, w97, w108],
  [w16, w39, w56, w73, w97, w108],
  [w16, w56, w82, w91, w97, w108, w114],
  [w30, w39, w56, w75, w97, w108]]
def b7_4 : List (List Sig) := [[w0, w16, w39, w56, w82, w97, w108],
  [w2, w16, w39, w47, w56, w82, w97],
  [w2, w16, w39, w56, w82, w99, w108],
  [w4, w16, w39, w56, w82, w97, w108],
  [w7, w16, w30, w39, w56, w97, w108],
  [w16, w30, w39, w56, w75, w97, w108],
  [w16, w31, w39, w56, w97, w108],
  [w16, w39, w45, w56, w82, w108],
  [w16, w39, w56, w80, w82, w97, w108],
  [w16, w39, w56, w82, w97, w103, w120],
  [w16, w39, w56, w82, w97, w106, w108],
  [w29, w39, w56, w75, w82, w97, w108]]
def b7_5 : List (List Sig) := [[w2, w14, w39, w56, w82, w97, w108],
  [w7, w39, w56, w75, w82, w97, w108],
  [w9, w16, w39, w56, w82, w97, w108],
  [w15, w16, w39, w56, w82, w97, w108],
  [w16, w18, w39, w56, w82, w97, w108],
  [w16, w30, w39, w82, w97, w108, w120],
  [w16, w39, w56, w82, w97, w110, w120],
  [w16, w53, w82, w91, w97, w108],
  [w16, w56, w82, w89, w97, w108],
  [w16, w82, w91, w97, w101, w108],
  [w35, w39, w56, w82, w97, w108],
  [w36, w39, w56, w82, w97, w108],
  [w56, w75, w82, w91, w97, w108]]
def b7_6 : List (List Sig) := [[w2, w16, w39, w56, w82, w97, w103],
  [w7, w16, w56, w82, w91, w97, w108],
  [w8, w16, w39, w56, w82, w97, w108],
  [w16, w21, w56, w82, w91, w97, w108],
  [w16, w39, w54, w82, w97, w108, w120],
  [w16, w39, w56, w82, w97, w108, w118],
  [w16, w56, w75, w82, w91, w97, w108],
  [w16, w60, w82, w91, w97, w108],
  [w39, w56, w74, w75, w82, w97, w108],
  [w39, w56, w75, w82, w91, w97, w108]]
def b7_7 : List (List Sig) := [[w1, w16, w39, w56, w82, w97, w108],
  [w2, w16, w39, w56, w82, w97, w110],
  [w7, w16, w39, w56, w82, w91, w97, w108],
  [w7, w16, w39, w56, w82, w94, w97],
  [w16, w17, w39, w56, w82, w97, w108],
  [w16, w30, w39, w56, w82, w97, w103, w108],
  [w16, w39, w48, w82, w97, w108],
  [w16, w39, w56, w64, w82, w97, w108, w120],
  [w16, w39, w56, w82, w97, w105, w108],
  [w39, w56, w75, w82, w92, w97, w108]]
def b7_8 : List (List Sig) := [[w2, w16, w39, w56, w71, w82, w108],
  [w7, w16, w39, w47, w56, w82, w97],
  [w7, w16, w39, w56, w82, w92, w97, w108],
  [w10, w16, w82, w91, w97, w108],
  [w16, w27, w56, w82, w91, w97, w108],
  [w16, w30, w39, w56, w82, w97, w108, w110],
  [w16, w39, w40, w56, w82, w97, w108],
  [w16, w39, w56, w57, w82, w97, w108],
  [w16, w39, w56, w66, w82, w97, w108],
  [w16, w42, w56, w82, w97, w108],
  [w16, w56, w82, w88, w97, w108],
  [w39, w56, w75, w84, w97, w108],
  [w39, w56, w75, w97, w108, w122],
  [w39, w56, w76, w82, w97, w108],
  [w39, w56, w82, w97, w104, w108]]
def b7_9 : List (List Sig) := [[w2, w16, w39, w44, w56, w82, w108],
  [w2, w16, w39, w56, w82, w97, w120],
  [w7, w14, w39, w56, w82, w97, w108],
  [w7, w16, w39, w56, w71, w97, w108],
  [w7, w16, w39, w56, w84, w97, w108],
  [w12, w16, w39, w56, w82, w97, w108],
  [w13, w16, w39, w56, w82, w97],
  [w14, w56, w82, w91, w97, w108],
  [w16, w28, w39, w56, w82, w97, w108],
  [w16, w39, w41, w56, w82, w97, w108],
  [w16, w39, w51, w56, w82, w97, w108],
  [w16, w39, w56, w65, w82, w97, w120],
  [w16, w39, w56, w68, w82, w97, w108],
  [w16, w39, w56, w82, w97, w108, w121],
  [w16, w56, w64, w82, w97, w108, w114],
  [w16, w56, w82, w87, w97, w108],
  [w39, w56, w59, w82, w97, w108],
  [w39, w56, w75, w78, w82, w97, w108]]
def b7_10 : List (List Sig) := [[w7, w39, w56, w75, w97, w108],
  [w16, w39, w56, w61, w82, w97, w108, w120],
  [w16, w39, w56, w81, w82, w97, w108],
  [w16, w39, w56, w82, w97, w114, w120],
  [w16, w39, w63, w82, w97, w108],
  [w16, w46, w56, w82, w97, w108],
  [w16, w56, w78, w82, w91, w97, w108],
  [w26, w39, w56, w82, w97, w108],
  [w39, w56, w60, w75, w82, w97, w108],
  [w39, w56, w75, w82, w94, w97, w108]]
def b7_11 : List (List Sig) := [[w2, w16, w39, w56, w65, w82, w97],
  [w7, w16, w39, w56, w60, w82, w97, w108],
  [w7, w16, w39, w56, w75, w97, w108],
  [w16, w30, w39, w56, w64, w97, w108],
  [w16, w30, w82, w91, w97, w108],
  [w16, w34, w39, w56, w82, w97, w108],
  [w16, w39, w44, w82, w97, w108, w120],
  [w16, w39, w82, w86, w97, w108],
  [w16, w56, w82, w91, w94, w97, w108],
  [w39, w47, w56, w75, w82, w97, w108]]
def b7_12 : List (List Sig) := [[w2, w16, w39, w56, w82, w92, w108],
  [w2, w16, w39, w56, w82, w97, w114],
  [w7, w16, w39, w56, w85, w97, w108],
  [w16, w25, w39, w56, w82, w97, w108],
  [w16, w30, w39, w56, w65, w82, w97, w108],
  [w16, w30, w39, w82, w91, w97, w108],
  [w16, w37, w56, w82, w97, w108, w120],
  [w16, w39, w52, w82, w97, w108, w120],
  [w16, w39, w56, w82, w97, w108, w113],
  [w16, w47, w56, w82, w91, w97, w108],
  [w16, w54, w82, w91, w97, w108],
  [w16, w56, w61, w82, w97, w108, w114],
  [w16, w56, w82, w90, w97, w108],
  [w16, w82, w91, w97, w108, w120]]
def b7_13 : List (List Sig) := [[w2, w16, w39, w56, w82, w98, w108],
  [w3, w16, w39, w56, w82, w97, w108],
  [w5, w16, w82, w91, w97, w108],
  [w7, w16, w39, w56, w82, w97, w120],
  [w13, w16, w39, w56, w82, w97, w108],
  [w16, w30, w39, w56, w82, w97, w108, w114],
  [w16, w39, w55, w56, w82, w97, w108],
  [w16, w39, w56, w71, w82, w97, w108, w110],
  [w16, w39, w56, w82, w97, w108, w109],
  [w16, w39, w56, w82, w97, w108, w120],
  [w16, w39, w82, w91, w97, w108, w120],
  [w16, w56, w64, w82, w91, w97, w108],
  [w16, w56, w82, w91, w97, w108, w121],
  [w39, w56, w75, w82, w97, w103, w108]]
def b7_14 : List (List Sig) := [[w2, w16, w37, w56, w82, w97, w108],
  [w2, w16, w39, w56, w82, w101, w108],
  [w6, w16, w39, w56, w82, w97, w108],
  [w7, w16, w33, w39, w56, w97, w108],
  [w11, w16, w39, w56, w82, w97, w108],
  [w16, w24, w39, w56, w82, w97, w108],
  [w16, w39, w50, w82, w97, w108, w120],
  [w16, w39, w56, w69, w82, w97, w108],
  [w16, w39, w56, w82, w97, w108, w111],
  [w16, w39, w56, w82, w97, w115],
  [w16, w43, w56, w82, w97, w108],
  [w16, w56, w62, w82, w97, w108],
  [w16, w56, w82, w91, w97, w103, w108],
  [w19, w39, w56, w82, w97, w108],
  [w39, w56, w75, w82, w97, w108, w110],
  [w39, w56, w75, w97, w108, w119],
  [w39, w56, w82, w93, w97, w108]]
def b7_15 : List (List Sig) := [[w2, w7, w16, w39, w56, w82, w97],
  [w2, w16, w39, w56, w82, w97, w108],
  [w7, w16, w39, w56, w65, w82, w97],
  [w16, w20, w39, w56, w82, w97, w108],
  [w16, w56, w67, w82, w97, w108],
  [w16, w56, w82, w91, w97, w108, w110]]
def b7_16 : List (List Sig) := [[w2, w16, w23, w39, w56, w82, w108],
  [w7, w16, w39, w56, w82, w97, w114],
  [w16, w25, w56, w82, w91, w97, w108],
  [w16, w30, w39, w60, w82, w97, w108],
  [w16, w39, w53, w82, w97, w108, w120],
  [w16, w39, w56, w79, w97, w108],
  [w16, w39, w56, w82, w97, w108, w117],
  [w16, w56, w61, w82, w91, w97, w108],
  [w23, w39, w56, w75, w97, w108],
  [w39, w56, w75, w82, w97, w108, w120],
  [w39, w56, w82, w92, w97, w108, w110]]
def tier7 : List (List (List Sig)) := [b7_0, b7_1, b7_2, b7_3, b7_4, b7_5, b7_6, b7_7, b7_8, b7_9, b7_10, b7_11, b7_12, b7_13, b7_14, b7_15, b7_16]
def b8_0 : List (List Sig) := [[w16, w39, w56, w71, w82, w97, w108],
  [w16, w39, w56, w82, w84, w97, w108],
  [w16, w39, w56, w82, w97, w108, w122]]
def b8_1 : List (List Sig) := [[w16, w39, w44, w56, w82, w97, w108],
  [w39, w56, w75, w82, w97, w108]]
def b8_2 : List (List Sig) := [[w7, w16, w39, w56, w82, w97, w108],
  [w16, w39, w52, w56, w82, w97, w108],
  [w16, w39, w56, w75, w82, w97, w108],
  [w16, w39, w56, w82, w97, w108, w112],
  [w16, w56, w82, w91, w97, w108]]
def b8_3 : List (List Sig) := [[w16, w39, w56, w82, w85, w97, w108],
  [w16, w39, w56, w82, w91, w97, w108]]
def b8_4 : List (List Sig) := [[w16, w39, w50, w56, w82, w97, w108],
  [w16, w39, w56, w82, w92, w97, w108]]
def b8_5 : List (List Sig) := [[w14, w39, w56, w82, w97, w108],
  [w16, w33, w39, w56, w82, w97, w108],
  [w16, w39, w56, w82, w97, w98, w108]]
def b8_6 : List (List Sig) := [[w16, w39, w53, w56, w82, w97, w108],
  [w16, w39, w56, w78, w82, w97, w108],
  [w16, w39, w56, w82, w97, w101, w108],
  [w16, w39, w56, w82, w97, w108, w119]]
def b8_7 : List (List Sig) := [[w16, w39, w56, w60, w82, w97, w108],
  [w16, w39, w56, w82, w94, w97, w108]]
def b8_8 : List (List Sig) := [[w16, w23, w39, w56, w82, w97, w108],
  [w16, w39, w47, w56, w82, w97, w108]]
def b8_9 : List (List Sig) := [[w10, w16, w39, w56, w82, w97, w108],
  [w16, w39, w49, w56, w82, w97, w108],
  [w16, w39, w56, w64, w82, w97, w108]]
def b8_10 : List (List Sig) := [[w16, w22, w39, w56, w82, w97, w108],
  [w16, w39, w56, w82, w97, w103, w108],
  [w16, w39, w56, w82, w97, w107, w108]]
def b8_11 : List (List Sig) := [[w16, w32, w39, w56, w82, w97, w108],
  [w16, w39, w56, w82, w97, w108, w110]]
def b8_12 : List (List Sig) := [[w16, w30, w39, w56, w82, w97, w108],
  [w16, w39, w56, w61, w82, w97, w108]]
def b8_13 : List (List Sig) := [[w16, w39, w54, w56, w82, w97, w108],
  [w16, w39, w56, w82, w97, w99, w108],
  [w16, w39, w56, w82, w97, w108, w120]]
def b8_14 : List (List Sig) := [[w5, w16, w39, w56, w82, w97, w108],
  [w16, w37, w56, w82, w97, w108]]
def b8_15 : List (List Sig) := [[w2, w16, w39, w56, w82, w97, w108],
  [w16, w39, w56, w65, w82, w97, w108]]
def b8_16 : List (List Sig) := [[w16, w39, w56, w82, w97, w108, w114]]
def tier8 : List (List (List Sig)) := [b8_0, b8_1, b8_2, b8_3, b8_4, b8_5, b8_6, b8_7, b8_8, b8_9, b8_10, b8_11, b8_12, b8_13, b8_14, b8_15, b8_16]
def b9_15 : List (List Sig) := [[w16, w39, w56, w82, w97, w108]]
def tier9 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], b9_15, []]
def buckets : ℕ → List (List (List Sig))
  | 1 => tier1
  | 2 => tier2
  | 3 => tier3
  | 4 => tier4
  | 5 => tier5
  | 6 => tier6
  | 7 => tier7
  | 8 => tier8
  | 9 => tier9
  | _ => []

def tiers (k : ℕ) := (buckets k).flatten
def lookup (k : ℕ) (w : List Sig) := bucketHas w (buckets k) (hashBucket w)
lemma lookup_sound (k : ℕ) (w : List Sig) (h : lookup k w = true) : w ∈ tiers k :=
  bucketHas_sound w (buckets k) (hashBucket w) h
end Minor0

namespace Minor6

def w0 : Sig := (0x4000400040004, 0x0)
def w1 : Sig := (0xc000c000c000c, 0x4f027813c09e04f)
def w2 : Sig := (0x12001200120012, 0x200100080040020)
def w3 : Sig := (0x18001800180018, 0x0)
def w4 : Sig := (0x18001800180018, 0xf507a83d41ea0f5)
def w5 : Sig := (0x24002400240024, 0x3431a18d0c686343)
def w6 : Sig := (0x40004000400040, 0x0)
def w7 : Sig := (0x48004800480048, 0x3451a28d1468a345)
def w8 : Sig := (0x5a005a005a005a, 0x2c01600b005802c)
def w9 : Sig := (0x60006000600060, 0x10f087843c21e10f)
def w10 : Sig := (0x6c006c006c006c, 0x34f1a78d3c69e34f)
def w11 : Sig := (0x7e007e007e007e, 0x36f1b78dbc6de36f)
def w12 : Sig := (0xc000c000c000c0, 0x13509a84d426a135)
def w13 : Sig := (0x110011001100110, 0x800400200100080)
def w14 : Sig := (0x11c011c011c011c, 0x2c01600b005802c0)
def w15 : Sig := (0x17c017c017c017c, 0x3cf1e78f3c79e3cf)
def w16 : Sig := (0x180018001800180, 0x3d11e88f447a23d1)
def w17 : Sig := (0x1d801d801d801d8, 0x3f51fa8fd47ea3f5)
def w18 : Sig := (0x1da01da01da01da, 0x3fd1fe8ff47fa3fd)
def w19 : Sig := (0x1dc01dc01dc01dc, 0x3f51fa8fd47ea3f5)
def w20 : Sig := (0x1e001e001e001e0, 0x3001800c00600300)
def w21 : Sig := (0x1ec01ec01ec01ec, 0x34f1a78d3c69e34f)
def w22 : Sig := (0x1f801f801f801f8, 0x3f51fa8fd47ea3f5)
def w23 : Sig := (0x1fa01fa01fa01fa, 0x32c1960cb065832c)
def w24 : Sig := (0x1fc01fc01fc01fc, 0x3c01e00f007803c0)
def w25 : Sig := (0x1fc01fc01fc01fc, 0x3ff1ff8ffc7fe3ff)
def w26 : Sig := (0x240024002400240, 0x505a82d416a0b505)
def w27 : Sig := (0x258025802580258, 0x240120090048024)
def w28 : Sig := (0x3d803d803d803d8, 0x3f51fa8fd47ea3f5)
def w29 : Sig := (0x402040204020402, 0x80040020010008)
def w30 : Sig := (0x600060006000600, 0x0)
def w31 : Sig := (0x600060006000600, 0xc0f607b03d81ec0f)
def w32 : Sig := (0x61a061a061a061a, 0x2c01600b005802c)
def w33 : Sig := (0x642064206420642, 0x2c01600b005802c)
def w34 : Sig := (0x648064806480648, 0xc006003001800c)
def w35 : Sig := (0x658065806580658, 0xc006003001800c)
def w36 : Sig := (0x658065806580658, 0x240120090048024)
def w37 : Sig := (0x658065806580658, 0x2c01600b005802c)
def w38 : Sig := (0x65a065a065a065a, 0x2c01600b005802c)
def w39 : Sig := (0x65e065e065e065e, 0x2c01600b005802c)
def w40 : Sig := (0x66c066c066c066c, 0x34f1a78d3c69e34f)
def w41 : Sig := (0x67e067e067e067e, 0x36f1b78dbc6de36f)
def w42 : Sig := (0x7da07da07da07da, 0x3fd1fe8ff47fa3fd)
def w43 : Sig := (0x7fa07fa07fa07fa, 0x32c1960cb065832c)
def w44 : Sig := (0xa000a000a000a00, 0x43521a90d486a435)
def w45 : Sig := (0x1004100410041004, 0xc43621b10d886c43)
def w46 : Sig := (0x101c101c101c101c, 0xc006003001800c0)
def w47 : Sig := (0x160c160c160c160c, 0xc4f627b13d89ec4f)
def w48 : Sig := (0x1800180018001800, 0x4d126893449a24d1)
def w49 : Sig := (0x1a181a181a181a18, 0x4f527a93d49ea4f5)
def w50 : Sig := (0x1e001e001e001e00, 0xc006003001800c00)
def w51 : Sig := (0x1e1c1e1c1e1c1e1c, 0xcff67fb3fd9fecff)
def w52 : Sig := (0x2020202020202020, 0x0)
def w53 : Sig := (0x2020202020202020, 0xd03e81f40fa07d03)
def w54 : Sig := (0x21e021e021e021e0, 0x3001800c00600300)
def w55 : Sig := (0x2400240024002400, 0x8004002001000800)
def w56 : Sig := (0x2424242424242424, 0x80a405202901480a)
def w57 : Sig := (0x246c246c246c246c, 0xb4f5a7ad3d69eb4f)
def w58 : Sig := (0x2660266026602660, 0xd0fe87f43fa1fd0f)
def w59 : Sig := (0x2662266226622662, 0xd2fe97f4bfa5fd2f)
def w60 : Sig := (0x2664266426642664, 0xd0fe87f43fa1fd0f)
def w61 : Sig := (0x2668266826682668, 0xd0fe87f43fa1fd0f)
def w62 : Sig := (0x266c266c266c266c, 0x80e407203901c80e)
def w63 : Sig := (0x266c266c266c266c, 0xf4ffa7fd3fe9ff4f)
def w64 : Sig := (0x267a267a267a267a, 0x2c01600b005802c)
def w65 : Sig := (0x267a267a267a267a, 0xd2fe97f4bfa5fd2f)
def w66 : Sig := (0x267e267e267e267e, 0x82e41720b905c82e)
def w67 : Sig := (0x4180418041804180, 0x0)
def w68 : Sig := (0x47da47da47da47da, 0x2c01600b005802c)
def w69 : Sig := (0x4800480048004800, 0x0)
def w70 : Sig := (0x4880488048804880, 0x511a88d446a23511)
def w71 : Sig := (0x4990499049904990, 0xb005802c01600b0)
def w72 : Sig := (0x49d849d849d849d8, 0x3f51fa8fd47ea3f5)
def w73 : Sig := (0x4ac04ac04ac04ac0, 0x535a9ad4d6a6b535)
def w74 : Sig := (0x4ad84ad84ad84ad8, 0x535a9ad4d6a6b535)
def w75 : Sig := (0x4bd04bd04bd04bd0, 0x5b5adad6d6b6b5b5)
def w76 : Sig := (0x4bd84bd84bd84bd8, 0xb405a02d01680b4)
def w77 : Sig := (0x4bd84bd84bd84bd8, 0x7f5bfadfd6feb7f5)
def w78 : Sig := (0x4e5a4e5a4e5a4e5a, 0x2c01600b005802c)
def w79 : Sig := (0x4ec24ec24ec24ec2, 0x53da9ed4f6a7b53d)
def w80 : Sig := (0x4eda4eda4eda4eda, 0x53da9ed4f6a7b53d)
def w81 : Sig := (0x4fda4fda4fda4fda, 0xbc05e02f01780bc)
def w82 : Sig := (0x5ad85ad85ad85ad8, 0x5f5afad7d6beb5f5)
def w83 : Sig := (0x60e060e060e060e0, 0x1008804402201100)
def w84 : Sig := (0x61e061e061e061e0, 0x1008804402201100)
def w85 : Sig := (0x61e061e061e061e0, 0x3009804c02601300)
def w86 : Sig := (0x66e066e066e066e0, 0xd0fe87f43fa1fd0f)
def w87 : Sig := (0x66e266e266e266e2, 0x12c89644b225912c)
def w88 : Sig := (0x66fa66fa66fa66fa, 0x12c89644b225912c)
def w89 : Sig := (0x6ae06ae06ae06ae0, 0x535a9ad4d6a6b535)
def w90 : Sig := (0x6e006e006e006e00, 0xc00e007003801c00)
def w91 : Sig := (0x6e606e606e606e60, 0xd0fe87f43fa1fd0f)
def w92 : Sig := (0x6ec06ec06ec06ec0, 0xd35e9af4d7a6bd35)
def w93 : Sig := (0x6ee06ee06ee06ee0, 0xd00e807403a01d00)
def w94 : Sig := (0x6ee06ee06ee06ee0, 0xd3fe9ff4ffa7fd3f)
def w95 : Sig := (0x8100810081008100, 0x2001000800400200)
def w96 : Sig := (0x875a875a875a875a, 0x22c11608b045822c)
def w97 : Sig := (0x9000900090009000, 0x0)
def w98 : Sig := (0x9000900090009000, 0x741ba0dd06e83741)
def w99 : Sig := (0x900c900c900c900c, 0x2401200900480240)
def w100 : Sig := (0x901c901c901c901c, 0xc006003001800c0)
def w101 : Sig := (0x901c901c901c901c, 0x2401200900480240)
def w102 : Sig := (0x901c901c901c901c, 0x2c01600b005802c0)
def w103 : Sig := (0x906c906c906c906c, 0x34f1a78d3c69e34f)
def w104 : Sig := (0x9104910491049104, 0x2c01600b005802c0)
def w105 : Sig := (0x9118911891189118, 0x2c01600b005802c0)
def w106 : Sig := (0x911c911c911c911c, 0x2c01600b005802c0)
def w107 : Sig := (0x915c915c915c915c, 0x2c01600b005802c0)
def w108 : Sig := (0x917c917c917c917c, 0x3cf1e78f3c79e3cf)
def w109 : Sig := (0x91d891d891d891d8, 0x3f51fa8fd47ea3f5)
def w110 : Sig := (0x91dc91dc91dc91dc, 0x3f51fa8fd47ea3f5)
def w111 : Sig := (0x91fc91fc91fc91fc, 0x3c01e00f007803c0)
def w112 : Sig := (0x9248924892489248, 0x745ba2dd16e8b745)
def w113 : Sig := (0x926c926c926c926c, 0x74fba7dd3ee9f74f)
def w114 : Sig := (0x93d893d893d893d8, 0x7f5bfadfd6feb7f5)
def w115 : Sig := (0x951e951e951e951e, 0x2c81640b205902c8)
def w116 : Sig := (0x964c964c964c964c, 0xf4ffa7fd3fe9ff4f)
def w117 : Sig := (0x965a965a965a965a, 0x2c01600b005802c)
def w118 : Sig := (0x971c971c971c971c, 0x2c01600b005802c0)
def w119 : Sig := (0x975e975e975e975e, 0x2ec1760bb05d82ec)
def w120 : Sig := (0x9a589a589a589a58, 0x7f5bfadfd6feb7f5)
def w121 : Sig := (0x9e009e009e009e00, 0xc006003001800c00)
def w122 : Sig := (0xa060a060a060a060, 0x3009804c02601300)
def w123 : Sig := (0xa06ca06ca06ca06c, 0x34f9a7cd3e69f34f)
def w124 : Sig := (0xa1e0a1e0a1e0a1e0, 0x3009804c02601300)
def w125 : Sig := (0xa660a660a660a660, 0xf0ff87fc3fe1ff0f)
def w126 : Sig := (0xa668a668a668a668, 0x30c9864c3261930c)
def w127 : Sig := (0xa67aa67aa67aa67a, 0x32c9964cb265932c)
def w128 : Sig := (0xb024b024b024b024, 0xf43fa1fd0fe87f43)
def w129 : Sig := (0xb02cb02cb02cb02c, 0xf43fa1fd0fe87f43)
def w130 : Sig := (0xb064b064b064b064, 0xf43fa1fd0fe87f43)
def w131 : Sig := (0xb06cb06cb06cb06c, 0x3409a04d02681340)
def w132 : Sig := (0xb06cb06cb06cb06c, 0xf4ffa7fd3fe9ff4f)
def w133 : Sig := (0xb124b124b124b124, 0xfc3fe1ff0ff87fc3)
def w134 : Sig := (0xb13cb13cb13cb13c, 0x2c01600b005802c0)
def w135 : Sig := (0xb13cb13cb13cb13c, 0xfc3fe1ff0ff87fc3)
def w136 : Sig := (0xb17cb17cb17cb17c, 0x3c09e04f027813c0)
def w137 : Sig := (0xb424b424b424b424, 0xf4bfa5fd2fe97f4b)
def w138 : Sig := (0xb42cb42cb42cb42c, 0xa4a5252929494a4a)
def w139 : Sig := (0xb51cb51cb51cb51c, 0xac05602b01580ac0)
def w140 : Sig := (0xb53cb53cb53cb53c, 0xaca5652b29594aca)
def w141 : Sig := (0xb600b600b600b600, 0xc00e007003801c00)
def w142 : Sig := (0xb624b624b624b624, 0xc0ae05702b815c0a)
def w143 : Sig := (0xb624b624b624b624, 0xf43fa1fd0fe87f43)
def w144 : Sig := (0xb62cb62cb62cb62c, 0xf4ffa7fd3fe9ff4f)
def w145 : Sig := (0xb660b660b660b660, 0xd0fe87f43fa1fd0f)
def w146 : Sig := (0xb660b660b660b660, 0xf00f807c03e01f00)
def w147 : Sig := (0xb664b664b664b664, 0xf4ffa7fd3fe9ff4f)
def w148 : Sig := (0xb668b668b668b668, 0xf4ffa7fd3fe9ff4f)
def w149 : Sig := (0xb66cb66cb66cb66c, 0xf4ffa7fd3fe9ff4f)
def w150 : Sig := (0xb67cb67cb67cb67c, 0xf4ffa7fd3fe9ff4f)
def w151 : Sig := (0xb67cb67cb67cb67c, 0xf6ffb7fdbfedff6f)
def w152 : Sig := (0xb67cb67cb67cb67c, 0xfcffe7ff3ff9ffcf)
def w153 : Sig := (0xb67eb67eb67eb67e, 0xf6ffb7fdbfedff6f)
def w154 : Sig := (0xb77cb77cb77cb77c, 0xfcffe7ff3ff9ffcf)
def w155 : Sig := (0xbe00be00be00be00, 0xc00e007003801c00)
def w156 : Sig := (0xc1c0c1c0c1c0c1c0, 0x3009804c02601300)
def w157 : Sig := (0xc1d8c1d8c1d8c1d8, 0x3f59facfd67eb3f5)
def w158 : Sig := (0xc3d8c3d8c3d8c3d8, 0x3249924c92649324)
def w159 : Sig := (0xc7dac7dac7dac7da, 0x32c9964cb265932c)
def w160 : Sig := (0xcbc0cbc0cbc0cbc0, 0x735b9adcd6e6b735)
def w161 : Sig := (0xd19cd19cd19cd19c, 0x2c01600b005802c0)
def w162 : Sig := (0xd1d8d1d8d1d8d1d8, 0x3c09e04f027813c0)
def w163 : Sig := (0xd1dcd1dcd1dcd1dc, 0x3c09e04f027813c0)
def w164 : Sig := (0xd91cd91cd91cd91c, 0x2c01600b005802c0)
def w165 : Sig := (0xd980d980d980d980, 0x7d1be8df46fa37d1)
def w166 : Sig := (0xd984d984d984d984, 0x7d1be8df46fa37d1)
def w167 : Sig := (0xd990d990d990d990, 0x7f1bf8dfc6fe37f1)
def w168 : Sig := (0xd998d998d998d998, 0x2f01780bc05e02f0)
def w169 : Sig := (0xd998d998d998d998, 0x7d1be8df46fa37d1)
def w170 : Sig := (0xd99cd99cd99cd99c, 0x2f01780bc05e02f0)
def w171 : Sig := (0xd99cd99cd99cd99c, 0x7d1be8df46fa37d1)
def w172 : Sig := (0xd9c0d9c0d9c0d9c0, 0x7d1be8df46fa37d1)
def w173 : Sig := (0xd9d8d9d8d9d8d9d8, 0x7f5bfadfd6feb7f5)
def w174 : Sig := (0xda00da00da00da00, 0x400a005002801400)
def w175 : Sig := (0xdac0dac0dac0dac0, 0x535a9ad4d6a6b535)
def w176 : Sig := (0xdac8dac8dac8dac8, 0x775bbaddd6eeb775)
def w177 : Sig := (0xdb80db80db80db80, 0x7d1be8df46fa37d1)
def w178 : Sig := (0xdb90db90db90db90, 0x4b0a5852c29614b0)
def w179 : Sig := (0xdb98db98db98db98, 0x7f5bfadfd6feb7f5)
def w180 : Sig := (0xdbc0dbc0dbc0dbc0, 0x700b805c02e01700)
def w181 : Sig := (0xdbc0dbc0dbc0dbc0, 0x7f5bfadfd6feb7f5)
def w182 : Sig := (0xdbd8dbd8dbd8dbd8, 0x7f5bfadfd6feb7f5)
def w183 : Sig := (0xdbdcdbdcdbdcdbdc, 0x7f5bfadfd6feb7f5)
def w184 : Sig := (0xde00de00de00de00, 0x400a005002801400)
def w185 : Sig := (0xde00de00de00de00, 0xc00e007003801c00)
def w186 : Sig := (0xdfd8dfd8dfd8dfd8, 0x7f5bfadfd6feb7f5)
def w187 : Sig := (0xdfd8dfd8dfd8dfd8, 0x7fdbfedff6ffb7fd)
def w188 : Sig := (0xdfd8dfd8dfd8dfd8, 0xff5ffaffd7febff5)
def w189 : Sig := (0xdfdadfdadfdadfda, 0x7fdbfedff6ffb7fd)
def w190 : Sig := (0xe000e000e000e000, 0x8004002001000)
def w191 : Sig := (0xe1a0e1a0e1a0e1a0, 0x3009804c02601300)
def w192 : Sig := (0xe1e0e1e0e1e0e1e0, 0x3009804c02601300)
def w193 : Sig := (0xe1e4e1e4e1e4e1e4, 0x3009804c02601300)
def w194 : Sig := (0xe1ece1ece1ece1ec, 0x34f9a7cd3e69f34f)
def w195 : Sig := (0xe1f2e1f2e1f2e1f2, 0x3209904c82641320)
def w196 : Sig := (0xe1f8e1f8e1f8e1f8, 0x3009804c02601300)
def w197 : Sig := (0xe1f8e1f8e1f8e1f8, 0x3f59facfd67eb3f5)
def w198 : Sig := (0xe1fae1fae1fae1fa, 0x32c9964cb265932c)
def w199 : Sig := (0xe1fce1fce1fce1fc, 0x3c09e04f027813c0)
def w200 : Sig := (0xe3f8e3f8e3f8e3f8, 0x3249924c92649324)
def w201 : Sig := (0xe5e2e5e2e5e2e5e2, 0x3089844c22611308)
def w202 : Sig := (0xe65ae65ae65ae65a, 0x2c81640b205902c)
def w203 : Sig := (0xe7e0e7e0e7e0e7e0, 0x3009804c02601300)
def w204 : Sig := (0xe7e0e7e0e7e0e7e0, 0xf0ff87fc3fe1ff0f)
def w205 : Sig := (0xe7e2e7e2e7e2e7e2, 0x32c9964cb265932c)
def w206 : Sig := (0xe7e8e7e8e7e8e7e8, 0x30c9864c3261930c)
def w207 : Sig := (0xe7fae7fae7fae7fa, 0x32c9964cb265932c)
def w208 : Sig := (0xe9e0e9e0e9e0e9e0, 0x3009804c02601300)
def w209 : Sig := (0xebe0ebe0ebe0ebe0, 0x735b9adcd6e6b735)
def w210 : Sig := (0xefe0efe0efe0efe0, 0xf00f807c03e01f00)
def w211 : Sig := (0xf1a4f1a4f1a4f1a4, 0x3c09e04f027813c0)
def w212 : Sig := (0xf1a4f1a4f1a4f1a4, 0xf43fa1fd0fe87f43)
def w213 : Sig := (0xf1bcf1bcf1bcf1bc, 0x3c09e04f027813c0)
def w214 : Sig := (0xf1e0f1e0f1e0f1e0, 0x3009804c02601300)
def w215 : Sig := (0xf1e4f1e4f1e4f1e4, 0x3c09e04f027813c0)
def w216 : Sig := (0xf1e4f1e4f1e4f1e4, 0xf43fa1fd0fe87f43)
def w217 : Sig := (0xf1ecf1ecf1ecf1ec, 0x3409a04d02681340)
def w218 : Sig := (0xf1f8f1f8f1f8f1f8, 0x3c09e04f027813c0)
def w219 : Sig := (0xf1fcf1fcf1fcf1fc, 0x3c09e04f027813c0)
def w220 : Sig := (0xf7e0f7e0f7e0f7e0, 0xf00f807c03e01f00)
def w221 : Sig := (0xf7ecf7ecf7ecf7ec, 0xf4ffa7fd3fe9ff4f)
def w222 : Sig := (0xf7fef7fef7fef7fe, 0x3ec9f64fb27d93ec)
def w223 : Sig := (0xf800f800f800f800, 0xc00e007003801c00)
def w224 : Sig := (0xf824f824f824f824, 0xf43fa1fd0fe87f43)
def w225 : Sig := (0xf980f980f980f980, 0xfd1fe8ff47fa3fd1)
def w226 : Sig := (0xf9a0f9a0f9a0f9a0, 0x7d1be8df46fa37d1)
def w227 : Sig := (0xf9a0f9a0f9a0f9a0, 0xf00f807c03e01f00)
def w228 : Sig := (0xf9a4f9a4f9a4f9a4, 0xfd3fe9ff4ffa7fd3)
def w229 : Sig := (0xf9e0f9e0f9e0f9e0, 0x7d1be8df46fa37d1)
def w230 : Sig := (0xf9e0f9e0f9e0f9e0, 0xf00f807c03e01f00)
def w231 : Sig := (0xfbe0fbe0fbe0fbe0, 0x700b805c02e01700)
def w232 : Sig := (0xfbf8fbf8fbf8fbf8, 0x7f5bfadfd6feb7f5)
def w233 : Sig := (0xfe00fe00fe00fe00, 0xc00e007003801c00)
def w234 : Sig := (0xfe04fe04fe04fe04, 0xc00e007003801c00)
def w235 : Sig := (0xfe12fe12fe12fe12, 0xc20e107083841c20)
def w236 : Sig := (0xfe18fe18fe18fe18, 0xc00e007003801c00)
def w237 : Sig := (0xfe20fe20fe20fe20, 0xc00e007003801c00)
def w238 : Sig := (0xfe24fe24fe24fe24, 0xc0ae05702b815c0a)
def w239 : Sig := (0xfe24fe24fe24fe24, 0xf43fa1fd0fe87f43)
def w240 : Sig := (0xfe40fe40fe40fe40, 0xc00e007003801c00)
def w241 : Sig := (0xfe5afe5afe5afe5a, 0xc2ce1670b3859c2c)
def w242 : Sig := (0xfe60fe60fe60fe60, 0xd0fe87f43fa1fd0f)
def w243 : Sig := (0xfe60fe60fe60fe60, 0xf00f807c03e01f00)
def w244 : Sig := (0xfe6cfe6cfe6cfe6c, 0xf4ffa7fd3fe9ff4f)
def w245 : Sig := (0xfec0fec0fec0fec0, 0xd35e9af4d7a6bd35)
def w246 : Sig := (0xfee0fee0fee0fee0, 0xd00e807403a01d00)
def w247 : Sig := (0xff10ff10ff10ff10, 0xc80e407203901c80)
def w248 : Sig := (0xff1cff1cff1cff1c, 0xec0f607b03d81ec0)
def w249 : Sig := (0xff80ff80ff80ff80, 0xc00e007003801c00)
def w250 : Sig := (0xff80ff80ff80ff80, 0xfd1fe8ff47fa3fd1)
def w251 : Sig := (0xff90ff90ff90ff90, 0xcb0e5872c3961cb0)
def w252 : Sig := (0xffa0ffa0ffa0ffa0, 0xf00f807c03e01f00)
def w253 : Sig := (0xffc0ffc0ffc0ffc0, 0xf00f807c03e01f00)
def w254 : Sig := (0xffd8ffd8ffd8ffd8, 0xff5ffaffd7febff5)
def w255 : Sig := (0xffe0ffe0ffe0ffe0, 0xf00f807c03e01f00)
def w256 : Sig := (0xfffafffafffafffa, 0xf2cf967cb3e59f2c)
def w257 : Sig := (0xfffcfffcfffcfffc, 0xfc0fe07f03f81fc0)
def w258 : Sig := (0xfffcfffcfffcfffc, 0xffffffffffffffff)
def tier1 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier2 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier3 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier4 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def tier5 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
def b6_0 : List (List Sig) := [[w4, w38, w106, w149, w182, w207, w233],
  [w10, w38, w106, w149, w182, w219, w255],
  [w38, w49, w73, w149, w192, w233, w248],
  [w38, w51, w106, w128, w182, w233],
  [w38, w58, w106, w122, w182, w233, w255],
  [w38, w106, w149, w180, w182, w219, w233],
  [w38, w106, w149, w182, w219, w249],
  [w106, w149, w165, w182, w203, w233],
  [w118, w149, w165, w182, w192, w233]]
def b6_1 : List (List Sig) := [[w17, w38, w106, w149, w156, w219, w233],
  [w31, w38, w106, w149, w182, w207, w233],
  [w38, w53, w73, w149, w182, w192, w233],
  [w38, w73, w98, w106, w149, w192, w233],
  [w38, w106, w128, w182, w219, w221, w233],
  [w106, w128, w149, w177, w182, w192, w233]]
def b6_2 : List (List Sig) := [[w24, w38, w58, w149, w182, w192, w233],
  [w31, w38, w106, w128, w182, w192, w233],
  [w38, w58, w106, w120, w192, w233],
  [w106, w128, w149, w182, w207, w219, w233]]
def b6_3 : List (List Sig) := [[w17, w38, w93, w106, w149, w182, w192],
  [w53, w106, w149, w165, w182, w192, w233]]
def b6_4 : List (List Sig) := [[w10, w17, w38, w106, w128, w182, w192],
  [w16, w106, w128, w149, w182, w192, w233],
  [w17, w38, w62, w106, w149, w192, w233],
  [w22, w38, w106, w149, w165, w192, w233],
  [w25, w38, w106, w149, w165, w192],
  [w38, w58, w149, w182, w192, w199, w233]]
def b6_5 : List (List Sig) := [[w10, w38, w106, w112, w182, w192, w241],
  [w10, w38, w106, w149, w182, w192, w257],
  [w10, w106, w128, w165, w182, w192, w233],
  [w17, w38, w66, w106, w149, w192, w233],
  [w38, w61, w149, w182, w192, w219, w233],
  [w38, w106, w120, w149, w219, w233],
  [w53, w106, w149, w182, w192, w207, w233],
  [w106, w128, w149, w181, w192, w233]]
def b6_6 : List (List Sig) := [[w17, w38, w106, w149, w182, w192, w210],
  [w38, w58, w73, w149, w165, w192, w233],
  [w38, w58, w81, w106, w182, w192, w233],
  [w38, w65, w149, w182, w192, w219, w233],
  [w38, w106, w149, w165, w192, w197, w233],
  [w106, w149, w165, w182, w192, w223, w255],
  [w117, w149, w182, w192, w219, w233]]
def b6_7 : List (List Sig) := [[w10, w38, w98, w106, w182, w192, w233],
  [w17, w38, w106, w132, w182, w192],
  [w38, w106, w131, w149, w182, w233, w255],
  [w106, w117, w149, w182, w192, w255],
  [w106, w128, w149, w182, w192, w236],
  [w106, w128, w149, w182, w196, w233]]
def b6_8 : List (List Sig) := [[w10, w16, w38, w106, w149, w182, w192],
  [w17, w38, w73, w149, w192, w219, w233],
  [w38, w58, w149, w182, w192, w233, w257],
  [w38, w106, w136, w149, w182, w233, w255],
  [w47, w106, w119, w149, w182, w207, w233],
  [w104, w128, w149, w182, w192, w219, w233],
  [w106, w132, w165, w182, w192, w233]]
def b6_9 : List (List Sig) := [[w17, w38, w73, w106, w149, w192, w255],
  [w17, w38, w134, w149, w192, w233],
  [w17, w64, w106, w149, w192, w233],
  [w38, w58, w149, w182, w207, w219, w233],
  [w38, w73, w149, w182, w219, w233, w255],
  [w38, w94, w149, w165, w192, w233]]
def b6_10 : List (List Sig) := [[w25, w38, w106, w128, w182, w192],
  [w38, w86, w106, w128, w182, w192, w233],
  [w38, w134, w149, w182, w233, w255],
  [w64, w106, w149, w182, w233, w255],
  [w106, w128, w149, w182, w192, w233, w250]]
def b6_11 : List (List Sig) := [[w8, w17, w106, w128, w149, w182, w192],
  [w14, w38, w58, w149, w182, w192, w255],
  [w17, w38, w56, w106, w128, w192, w233],
  [w17, w38, w90, w149, w182, w192, w219],
  [w17, w38, w106, w149, w182, w207, w255],
  [w17, w106, w149, w165, w192, w207, w233],
  [w28, w38, w106, w149, w182, w192, w255],
  [w38, w51, w106, w149, w165, w233],
  [w38, w58, w76, w106, w182, w192, w233],
  [w38, w63, w182, w192, w219, w233],
  [w38, w73, w112, w119, w149, w192, w233],
  [w38, w77, w149, w192, w219, w233],
  [w58, w68, w106, w182, w192, w233]]
def b6_12 : List (List Sig) := [[w4, w38, w106, w149, w165, w192, w233],
  [w31, w38, w106, w149, w182, w233, w255],
  [w38, w58, w71, w106, w165, w192, w233],
  [w38, w58, w73, w128, w182, w192, w233],
  [w38, w58, w149, w181, w192, w233],
  [w38, w63, w106, w182, w192, w255],
  [w38, w77, w106, w149, w192, w255],
  [w38, w106, w149, w165, w232, w233, w255],
  [w49, w106, w149, w182, w207, w233, w241],
  [w106, w149, w165, w182, w207, w233, w255]]
def b6_13 : List (List Sig) := [[w10, w38, w58, w182, w192, w219, w233],
  [w17, w38, w98, w106, w149, w192, w233],
  [w38, w106, w128, w182, w192, w204, w233]]
def b6_14 : List (List Sig) := [[w10, w38, w58, w106, w182, w192, w255],
  [w33, w58, w149, w165, w182, w192, w233],
  [w38, w58, w106, w182, w192, w249],
  [w38, w58, w149, w182, w192, w236],
  [w38, w58, w149, w182, w196, w233],
  [w38, w73, w149, w182, w192, w233, w257],
  [w68, w106, w149, w182, w219, w233],
  [w106, w129, w149, w165, w182, w192, w233]]
def b6_15 : List (List Sig) := [[w4, w38, w73, w106, w149, w192, w233],
  [w10, w17, w38, w106, w149, w165, w192],
  [w17, w38, w106, w116, w192, w233],
  [w17, w38, w106, w149, w182, w192, w257],
  [w38, w94, w128, w182, w192, w233],
  [w106, w135, w149, w165, w182, w192, w233]]
def b6_16 : List (List Sig) := [[w4, w38, w106, w149, w182, w219, w233],
  [w17, w38, w106, w149, w182, w203],
  [w17, w38, w118, w149, w182, w192],
  [w38, w53, w149, w182, w192, w219, w233],
  [w38, w58, w98, w106, w182, w192, w233],
  [w38, w106, w116, w182, w233, w255],
  [w58, w106, w128, w182, w192, w207, w233],
  [w73, w106, w128, w149, w165, w192, w233]]
def tier6 : List (List (List Sig)) := [b6_0, b6_1, b6_2, b6_3, b6_4, b6_5, b6_6, b6_7, b6_8, b6_9, b6_10, b6_11, b6_12, b6_13, b6_14, b6_15, b6_16]
def b7_0 : List (List Sig) := [[w8, w106, w128, w149, w182, w192, w233],
  [w8, w106, w149, w182, w192, w207, w233],
  [w10, w38, w106, w153, w182, w192, w233],
  [w10, w38, w106, w154, w182, w192, w233],
  [w11, w38, w106, w149, w182, w192, w233],
  [w15, w38, w106, w149, w182, w192, w233],
  [w17, w38, w56, w106, w149, w192, w233],
  [w17, w38, w73, w106, w149, w192, w233],
  [w17, w38, w106, w112, w149, w192, w233],
  [w30, w106, w149, w165, w182, w192, w233],
  [w36, w106, w149, w182, w192, w233],
  [w38, w49, w73, w106, w149, w192, w233],
  [w38, w77, w106, w149, w182, w192, w233],
  [w38, w81, w106, w149, w182, w192, w233],
  [w38, w90, w149, w182, w192, w219, w233],
  [w38, w100, w149, w182, w192, w233],
  [w38, w106, w113, w182, w192, w233],
  [w38, w106, w122, w149, w182, w207, w233],
  [w38, w106, w127, w149, w182, w192, w233],
  [w38, w106, w149, w160, w182, w192, w233],
  [w38, w106, w149, w182, w192, w194, w233],
  [w38, w106, w149, w182, w192, w198, w233],
  [w38, w106, w149, w182, w192, w199, w233],
  [w38, w106, w149, w182, w192, w225, w233],
  [w38, w106, w149, w182, w192, w233, w242],
  [w38, w106, w149, w182, w192, w233, w253],
  [w38, w106, w149, w182, w207, w233, w255],
  [w38, w106, w151, w182, w192, w233],
  [w38, w149, w161, w182, w192, w233],
  [w104, w106, w128, w149, w182, w192, w233]]
def b7_1 : List (List Sig) := [[w10, w38, w106, w149, w165, w182, w192, w233],
  [w17, w38, w106, w149, w182, w192, w255],
  [w18, w38, w106, w149, w182, w192, w233],
  [w27, w106, w128, w149, w182, w192, w233],
  [w27, w106, w149, w182, w192, w207, w233],
  [w38, w49, w106, w149, w182, w219, w233],
  [w38, w58, w73, w149, w182, w192, w233],
  [w38, w62, w106, w149, w182, w192, w233],
  [w38, w73, w106, w128, w149, w182, w192, w233],
  [w38, w106, w110, w149, w182, w192, w233],
  [w38, w106, w121, w149, w182, w192],
  [w38, w106, w134, w149, w182, w192, w233],
  [w38, w106, w149, w156, w182, w192, w233, w248],
  [w38, w106, w149, w182, w192, w197, w233],
  [w38, w106, w149, w182, w192, w200, w233],
  [w38, w106, w149, w182, w192, w220, w233],
  [w38, w106, w149, w182, w192, w241, w255],
  [w38, w119, w149, w182, w192, w219, w233],
  [w38, w139, w149, w182, w192, w233]]
def b7_2 : List (List Sig) := [[w10, w38, w106, w149, w182, w192, w219, w233],
  [w14, w38, w58, w149, w182, w192, w233],
  [w28, w38, w106, w149, w182, w192, w233],
  [w33, w38, w58, w149, w182, w192, w233],
  [w38, w49, w106, w149, w182, w192, w223, w233],
  [w38, w49, w106, w149, w182, w207, w233],
  [w38, w58, w106, w128, w182, w192, w233],
  [w38, w59, w149, w182, w192, w233],
  [w38, w66, w106, w149, w182, w192, w233],
  [w38, w71, w106, w119, w149, w182, w192, w233],
  [w38, w73, w106, w149, w165, w192, w233],
  [w38, w106, w122, w149, w182, w192, w233, w248],
  [w38, w106, w129, w149, w182, w192, w233],
  [w38, w106, w133, w149, w182, w192, w233],
  [w38, w106, w149, w167, w182, w192, w233],
  [w38, w106, w149, w182, w185, w192],
  [w38, w106, w149, w182, w192, w204, w233]]
def b7_3 : List (List Sig) := [[w7, w38, w106, w149, w182, w192, w233],
  [w10, w38, w106, w149, w182, w192, w223],
  [w17, w38, w90, w106, w149, w182, w192],
  [w33, w38, w106, w112, w149, w182, w192, w233],
  [w35, w106, w149, w182, w192, w233],
  [w38, w44, w106, w149, w182, w192, w233],
  [w38, w58, w106, w112, w182, w192, w233],
  [w38, w63, w106, w182, w192, w233],
  [w38, w70, w106, w149, w182, w192, w233],
  [w38, w73, w119, w149, w182, w192, w233],
  [w38, w77, w106, w149, w192, w233],
  [w38, w101, w149, w182, w192, w233],
  [w38, w106, w131, w149, w182, w192, w233],
  [w38, w106, w135, w149, w182, w192, w233],
  [w38, w106, w147, w182, w192, w233],
  [w38, w106, w149, w165, w192, w233, w254],
  [w38, w106, w149, w175, w182, w192, w233],
  [w38, w106, w149, w182, w184, w192],
  [w38, w106, w149, w182, w192, w232, w233, w241]]
def b7_4 : List (List Sig) := [[w17, w38, w106, w149, w189, w192, w233],
  [w38, w49, w106, w149, w182, w192, w233, w248],
  [w38, w83, w106, w149, w182, w233, w255],
  [w38, w94, w149, w182, w192, w233],
  [w38, w102, w149, w182, w192, w233],
  [w38, w106, w111, w149, w182, w192, w233],
  [w38, w106, w123, w149, w182, w192, w233],
  [w38, w106, w136, w149, w182, w192, w233],
  [w38, w106, w141, w149, w182, w192, w255],
  [w38, w106, w149, w157, w182, w192, w233],
  [w38, w106, w149, w158, w182, w192, w233],
  [w38, w106, w149, w177, w182, w192, w233],
  [w38, w106, w149, w182, w192, w196, w233],
  [w38, w106, w149, w182, w192, w222, w233],
  [w38, w106, w149, w182, w192, w233, w251],
  [w38, w106, w149, w182, w192, w233, w256],
  [w38, w106, w149, w182, w192, w233, w257],
  [w38, w106, w149, w182, w201, w233],
  [w38, w106, w149, w182, w214, w233],
  [w38, w106, w150, w182, w192, w233],
  [w38, w115, w149, w182, w192, w233]]
def b7_5 : List (List Sig) := [[w10, w38, w58, w106, w182, w192, w233],
  [w10, w38, w106, w149, w182, w192, w248],
  [w25, w38, w106, w149, w182, w192, w233],
  [w38, w46, w58, w149, w182, w192, w233],
  [w38, w47, w106, w119, w149, w182, w192, w233],
  [w38, w56, w73, w106, w149, w192, w233],
  [w38, w58, w105, w149, w182, w192, w233],
  [w38, w73, w106, w112, w149, w192, w233],
  [w38, w73, w149, w182, w192, w219, w233],
  [w38, w76, w106, w149, w182, w192, w233],
  [w38, w103, w106, w149, w182, w192, w233],
  [w38, w106, w128, w182, w192, w233, w258],
  [w38, w106, w137, w182, w192, w233],
  [w38, w106, w138, w149, w182, w192, w233],
  [w38, w106, w146, w149, w182, w192, w233],
  [w38, w106, w149, w167, w192, w233],
  [w38, w106, w149, w181, w182, w192, w233],
  [w38, w106, w149, w182, w192, w229, w233],
  [w38, w106, w149, w182, w192, w231, w233],
  [w38, w106, w149, w182, w192, w233, w237],
  [w38, w106, w149, w182, w203, w233],
  [w38, w106, w149, w182, w207, w219, w233],
  [w38, w106, w149, w182, w217, w233],
  [w38, w106, w152, w182, w192, w233],
  [w38, w118, w149, w182, w192, w233],
  [w68, w106, w149, w182, w192, w233],
  [w106, w119, w149, w165, w182, w192, w233]]
def b7_6 : List (List Sig) := [[w1, w38, w106, w149, w182, w192, w233],
  [w5, w38, w106, w149, w182, w192, w233],
  [w12, w38, w106, w149, w182, w192, w233],
  [w17, w38, w106, w141, w149, w182, w192],
  [w26, w38, w106, w149, w182, w192, w233],
  [w38, w51, w106, w149, w182, w233],
  [w38, w58, w106, w149, w182, w192, w233, w255],
  [w38, w71, w106, w149, w165, w192, w233],
  [w38, w73, w106, w149, w192, w233, w254],
  [w38, w82, w106, w149, w192, w233],
  [w38, w92, w106, w149, w182, w192, w233],
  [w38, w97, w149, w182, w192, w219, w233],
  [w38, w106, w108, w149, w182, w192, w233],
  [w38, w106, w114, w149, w192, w233],
  [w38, w106, w125, w149, w182, w192, w233],
  [w38, w106, w132, w149, w182, w192, w233],
  [w38, w106, w140, w149, w182, w192, w233],
  [w38, w106, w148, w182, w192, w233],
  [w38, w106, w149, w182, w192, w216, w233],
  [w38, w106, w149, w182, w192, w240],
  [w38, w107, w149, w182, w192, w233],
  [w38, w134, w149, w182, w192, w233],
  [w64, w106, w149, w182, w192, w233],
  [w106, w128, w149, w182, w192, w233, w241],
  [w106, w149, w182, w192, w207, w233, w241]]
def b7_7 : List (List Sig) := [[w3, w106, w128, w149, w182, w192, w233],
  [w4, w38, w106, w149, w182, w192, w233],
  [w10, w38, w106, w149, w174, w182, w192],
  [w14, w38, w106, w149, w182, w192, w255],
  [w16, w38, w106, w149, w182, w192, w233],
  [w17, w38, w50, w106, w149, w182, w192],
  [w38, w58, w71, w106, w182, w192, w233],
  [w38, w97, w106, w149, w182, w192, w255],
  [w38, w106, w149, w157, w192, w233],
  [w38, w106, w149, w182, w192, w233, w255],
  [w38, w106, w149, w182, w219, w221, w233],
  [w38, w106, w149, w182, w232, w233, w255],
  [w106, w119, w149, w182, w192, w207, w233],
  [w106, w149, w182, w192, w228, w233]]
def b7_8 : List (List Sig) := [[w8, w38, w106, w112, w149, w182, w192, w233],
  [w10, w38, w106, w149, w182, w192, w255],
  [w14, w38, w73, w149, w182, w192, w233],
  [w31, w38, w106, w149, w182, w192, w233],
  [w38, w47, w106, w149, w182, w233, w255],
  [w38, w53, w106, w149, w182, w192, w233],
  [w38, w56, w106, w128, w182, w192, w233],
  [w38, w57, w106, w149, w182, w192, w233],
  [w38, w58, w106, w149, w182, w192, w233],
  [w38, w58, w149, w182, w192, w233, w248],
  [w38, w106, w142, w149, w182, w192, w233],
  [w38, w106, w149, w165, w192, w232, w233],
  [w38, w106, w149, w172, w182, w192, w233],
  [w38, w106, w149, w176, w192, w233],
  [w38, w106, w149, w180, w182, w192, w233],
  [w38, w106, w149, w181, w192, w233],
  [w38, w106, w149, w182, w192, w226, w233],
  [w38, w106, w149, w182, w192, w233, w243],
  [w38, w106, w149, w182, w192, w249],
  [w106, w128, w149, w165, w182, w192, w233],
  [w106, w149, w165, w182, w192, w207, w233]]
def b7_9 : List (List Sig) := [[w17, w38, w52, w106, w149, w192, w233],
  [w17, w38, w106, w149, w156, w192, w233],
  [w17, w38, w106, w149, w182, w192, w233],
  [w38, w49, w90, w106, w149, w182, w192, w233],
  [w38, w49, w106, w149, w182, w192, w233, w241],
  [w38, w58, w106, w153, w182, w192, w233],
  [w38, w73, w106, w149, w189, w192, w233],
  [w38, w79, w106, w149, w182, w192, w233],
  [w38, w87, w106, w149, w182, w192, w233],
  [w38, w93, w106, w149, w182, w192, w233],
  [w38, w105, w149, w182, w192, w219, w233],
  [w38, w106, w128, w182, w192, w221, w233],
  [w38, w106, w143, w149, w182, w192, w233],
  [w38, w106, w149, w165, w182, w192, w233, w255],
  [w38, w106, w149, w168, w182, w192, w233],
  [w38, w106, w149, w182, w192, w212, w233],
  [w38, w106, w149, w182, w192, w218, w233],
  [w38, w106, w149, w182, w192, w246],
  [w38, w111, w149, w182, w192, w233]]
def b7_10 : List (List Sig) := [[w10, w17, w38, w106, w149, w182, w192],
  [w10, w38, w90, w106, w149, w182, w192],
  [w10, w38, w106, w128, w182, w192, w233],
  [w10, w38, w106, w149, w182, w192, w241],
  [w14, w38, w47, w106, w149, w182, w192, w233],
  [w20, w38, w106, w149, w182, w219, w233],
  [w33, w106, w149, w165, w182, w192, w233],
  [w34, w106, w149, w165, w182, w192, w233],
  [w38, w52, w106, w149, w182, w233, w255],
  [w38, w58, w106, w149, w165, w182, w192, w233],
  [w38, w80, w106, w149, w182, w192, w233],
  [w38, w83, w106, w149, w182, w207, w233],
  [w38, w88, w106, w149, w182, w192, w233],
  [w38, w98, w106, w149, w182, w192, w233],
  [w38, w106, w130, w149, w182, w192, w233],
  [w38, w106, w149, w182, w191, w233, w255],
  [w38, w106, w149, w182, w192, w233, w252],
  [w38, w106, w149, w182, w192, w235],
  [w38, w106, w149, w182, w192, w236],
  [w38, w106, w149, w182, w192, w247],
  [w38, w106, w149, w182, w195, w233],
  [w38, w106, w149, w182, w196, w233],
  [w106, w128, w149, w182, w192, w207, w233],
  [w106, w149, w182, w192, w225, w233]]
def b7_11 : List (List Sig) := [[w9, w38, w106, w149, w182, w192, w233],
  [w10, w38, w106, w112, w182, w192, w233],
  [w20, w38, w106, w149, w182, w207, w233],
  [w38, w43, w106, w149, w182, w192, w233],
  [w38, w46, w73, w149, w182, w192, w233],
  [w38, w48, w106, w149, w182, w192, w233],
  [w38, w58, w67, w106, w182, w192, w233],
  [w38, w58, w106, w182, w192, w233, w244],
  [w38, w60, w106, w149, w182, w192, w233],
  [w38, w73, w106, w149, w192, w232, w233],
  [w38, w84, w106, w149, w182, w233],
  [w38, w89, w106, w149, w182, w192, w233],
  [w38, w91, w106, w149, w182, w192, w233],
  [w38, w99, w149, w182, w192, w219, w233],
  [w38, w104, w149, w182, w192, w219, w233],
  [w38, w106, w122, w149, w182, w233, w255],
  [w38, w106, w149, w165, w182, w192, w233],
  [w38, w106, w149, w182, w192, w215, w233],
  [w38, w106, w149, w182, w192, w223, w255],
  [w38, w106, w149, w182, w192, w230, w233],
  [w38, w106, w149, w182, w192, w233, w238],
  [w38, w106, w149, w182, w231, w233],
  [w38, w106, w149, w187, w192, w233],
  [w38, w106, w149, w188, w192, w233],
  [w106, w149, w182, w192, w202, w233]]
def b7_12 : List (List Sig) := [[w17, w38, w106, w149, w182, w192, w219, w233],
  [w17, w38, w106, w149, w183, w192, w233],
  [w18, w38, w106, w149, w182, w192],
  [w19, w38, w106, w149, w182, w192, w233],
  [w33, w106, w149, w182, w192, w207, w233],
  [w34, w106, w149, w182, w192, w207, w233],
  [w38, w40, w106, w149, w182, w192, w233],
  [w38, w45, w106, w149, w182, w192, w233],
  [w38, w58, w106, w149, w182, w192, w207, w233],
  [w38, w68, w106, w149, w182, w192, w233],
  [w38, w72, w106, w149, w182, w192, w233],
  [w38, w73, w106, w149, w182, w192, w233, w255],
  [w38, w106, w116, w182, w192, w233],
  [w38, w106, w124, w149, w182, w233],
  [w38, w106, w144, w182, w192, w233],
  [w38, w106, w149, w155, w182, w192],
  [w38, w106, w149, w161, w182, w192, w233],
  [w38, w106, w149, w162, w182, w192, w233],
  [w38, w106, w149, w169, w182, w192, w233],
  [w38, w106, w149, w170, w182, w192, w233],
  [w38, w106, w149, w178, w182, w192, w233],
  [w38, w106, w149, w179, w192, w233],
  [w38, w106, w149, w182, w192, w205, w233],
  [w38, w106, w149, w182, w192, w206, w233],
  [w38, w106, w149, w182, w192, w210, w233],
  [w38, w106, w149, w182, w192, w219, w233],
  [w38, w106, w149, w182, w192, w233, w239],
  [w38, w106, w149, w182, w192, w233, w245],
  [w38, w106, w149, w182, w192, w234],
  [w38, w106, w149, w182, w193, w233],
  [w38, w106, w149, w186, w192, w233],
  [w38, w149, w164, w182, w192, w233],
  [w39, w106, w149, w182, w192, w233],
  [w78, w106, w149, w182, w192, w233],
  [w96, w106, w149, w182, w192, w233],
  [w106, w133, w149, w182, w192, w233]]
def b7_13 : List (List Sig) := [[w17, w38, w106, w128, w149, w182, w192, w233],
  [w17, w38, w106, w149, w182, w192, w207, w233],
  [w38, w41, w106, w149, w182, w192, w233],
  [w38, w58, w106, w122, w182, w192, w233],
  [w38, w63, w106, w149, w182, w192, w233],
  [w38, w64, w106, w149, w182, w192, w233],
  [w38, w73, w99, w149, w182, w192, w233],
  [w38, w73, w104, w149, w182, w192, w233],
  [w38, w106, w120, w149, w192, w233],
  [w38, w106, w125, w182, w192, w233],
  [w38, w106, w128, w149, w182, w192, w233],
  [w38, w106, w132, w182, w192, w233],
  [w38, w106, w147, w149, w182, w192, w233],
  [w38, w106, w149, w173, w182, w192, w233],
  [w38, w106, w149, w182, w192, w207, w233],
  [w38, w106, w149, w182, w192, w233, w250]]
def b7_14 : List (List Sig) := [[w3, w38, w58, w149, w182, w192, w233],
  [w8, w17, w38, w106, w149, w182, w192],
  [w10, w38, w50, w106, w149, w182, w192],
  [w17, w38, w106, w149, w165, w192, w233],
  [w32, w106, w149, w165, w182, w192, w233],
  [w38, w42, w106, w149, w182, w192, w233],
  [w38, w47, w106, w149, w182, w207, w233],
  [w38, w49, w106, w149, w165, w192, w233],
  [w38, w54, w106, w149, w182, w233],
  [w38, w56, w106, w149, w182, w192, w233, w241],
  [w38, w59, w106, w149, w182, w192, w233],
  [w38, w61, w106, w149, w182, w192, w233],
  [w38, w67, w106, w149, w182, w219, w233],
  [w38, w73, w106, w149, w182, w192, w233],
  [w38, w73, w149, w182, w192, w233, w248],
  [w38, w106, w112, w149, w182, w192, w233, w241],
  [w38, w106, w128, w154, w182, w192, w233],
  [w38, w106, w145, w149, w182, w192, w233],
  [w38, w106, w149, w165, w183, w192, w233],
  [w38, w106, w149, w166, w182, w192, w233],
  [w38, w106, w149, w182, w192, w209, w233],
  [w38, w106, w149, w182, w192, w211, w233],
  [w38, w106, w149, w182, w192, w227, w233],
  [w38, w106, w149, w182, w192, w228, w233],
  [w38, w106, w149, w182, w192, w233, w249],
  [w106, w149, w165, w182, w192, w223, w233]]
def b7_15 : List (List Sig) := [[w10, w38, w71, w106, w182, w192, w233],
  [w17, w38, w106, w149, w182, w192, w248],
  [w21, w38, w106, w149, w182, w192, w233],
  [w23, w38, w106, w149, w182, w192, w233],
  [w24, w38, w106, w149, w182, w192, w233],
  [w38, w47, w104, w106, w149, w182, w192, w233],
  [w38, w47, w106, w128, w182, w192, w233],
  [w38, w65, w106, w149, w182, w192, w233],
  [w38, w74, w106, w149, w182, w192, w233],
  [w38, w75, w106, w149, w182, w192, w233],
  [w38, w85, w106, w149, w182, w233],
  [w38, w106, w109, w149, w182, w192, w233],
  [w38, w106, w112, w119, w149, w182, w192, w233],
  [w38, w106, w137, w149, w182, w192, w233],
  [w38, w106, w149, w156, w182, w219, w233],
  [w38, w106, w149, w163, w182, w192, w233],
  [w38, w106, w149, w171, w182, w192, w233],
  [w38, w106, w149, w174, w182, w192, w255],
  [w38, w106, w149, w182, w191, w219, w233],
  [w38, w106, w149, w182, w192, w213, w233],
  [w38, w106, w149, w182, w192, w214, w233],
  [w38, w106, w149, w182, w192, w233, w246],
  [w38, w106, w149, w182, w208, w233],
  [w106, w117, w149, w182, w192, w233]]
def b7_16 : List (List Sig) := [[w10, w38, w106, w149, w182, w192, w233],
  [w17, w30, w38, w106, w149, w182, w192],
  [w22, w38, w106, w149, w182, w192, w233],
  [w25, w38, w106, w149, w182, w192],
  [w32, w106, w128, w149, w182, w192, w233],
  [w37, w106, w149, w182, w192, w233],
  [w38, w47, w106, w149, w182, w192, w233, w248],
  [w38, w58, w149, w182, w192, w219, w233],
  [w38, w86, w106, w149, w182, w192, w233],
  [w38, w94, w106, w149, w182, w192, w233],
  [w38, w106, w119, w149, w182, w192, w221, w233],
  [w38, w106, w126, w149, w182, w192, w233],
  [w38, w106, w128, w149, w182, w192, w219, w233],
  [w38, w106, w128, w182, w192, w233, w244],
  [w38, w106, w149, w156, w182, w207, w233],
  [w38, w106, w149, w159, w182, w192, w233],
  [w38, w106, w149, w165, w192, w233, w258],
  [w38, w106, w149, w173, w192, w233],
  [w38, w106, w149, w182, w192, w203, w233],
  [w38, w106, w149, w182, w192, w217, w233],
  [w38, w106, w149, w182, w192, w224, w233],
  [w38, w106, w149, w182, w192, w237],
  [w38, w106, w149, w182, w219, w233, w255]]
def tier7 : List (List (List Sig)) := [b7_0, b7_1, b7_2, b7_3, b7_4, b7_5, b7_6, b7_7, b7_8, b7_9, b7_10, b7_11, b7_12, b7_13, b7_14, b7_15, b7_16]
def b8_0 : List (List Sig) := [[w38, w83, w106, w149, w182, w192, w233]]
def b8_1 : List (List Sig) := [[w20, w38, w106, w149, w182, w192, w233],
  [w38, w46, w106, w149, w182, w192, w233],
  [w38, w55, w106, w149, w182, w192, w233],
  [w38, w71, w106, w149, w182, w192, w233],
  [w38, w105, w106, w149, w182, w192, w233],
  [w38, w106, w149, w182, w189, w192, w233]]
def b8_2 : List (List Sig) := [[w32, w38, w106, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w223, w233]]
def b8_3 : List (List Sig) := [[w8, w38, w106, w149, w182, w192, w233],
  [w38, w99, w106, w149, w182, w192, w233],
  [w38, w104, w106, w149, w182, w192, w233],
  [w38, w106, w149, w153, w182, w192, w233],
  [w38, w106, w149, w154, w182, w192, w233],
  [w38, w106, w149, w182, w192, w232, w233]]
def b8_4 : List (List Sig) := [[w27, w38, w106, w149, w182, w192, w233],
  [w29, w38, w106, w149, w182, w192, w233],
  [w38, w47, w106, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w233, w248]]
def b8_5 : List (List Sig) := [[w30, w38, w106, w149, w182, w192, w233],
  [w38, w67, w106, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w233, w244]]
def b8_6 : List (List Sig) := [[w6, w38, w106, w149, w182, w192, w233],
  [w38, w52, w106, w149, w182, w192, w233],
  [w38, w106, w149, w156, w182, w192, w233],
  [w38, w106, w149, w174, w182, w192, w233],
  [w38, w106, w149, w182, w191, w192, w233]]
def b8_7 : List (List Sig) := [[w38, w106, w122, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w233, w255]]
def b8_8 : List (List Sig) := [[w38, w58, w106, w149, w182, w192, w233]]
def b8_9 : List (List Sig) := [[w17, w38, w106, w149, w182, w192, w233],
  [w38, w49, w106, w149, w182, w192, w233],
  [w38, w90, w106, w149, w182, w192, w233],
  [w38, w106, w149, w182, w183, w192, w233],
  [w38, w106, w149, w182, w192, w233, w241]]
def b8_10 : List (List Sig) := [[w2, w38, w106, w149, w182, w192, w233],
  [w3, w38, w106, w149, w182, w192, w233],
  [w13, w38, w106, w149, w182, w192, w233],
  [w38, w106, w119, w149, w182, w192, w233]]
def b8_11 : List (List Sig) := [[w38, w106, w149, w165, w182, w192, w233],
  [w38, w106, w149, w182, w190, w192, w233],
  [w38, w106, w149, w182, w192, w233, w258]]
def b8_12 : List (List Sig) := [[w0, w38, w106, w149, w182, w192, w233],
  [w38, w69, w106, w149, w182, w192, w233],
  [w38, w95, w106, w149, w182, w192, w233],
  [w38, w106, w141, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w219, w233]]
def b8_13 : List (List Sig) := [[w38, w50, w106, w149, w182, w192, w233],
  [w38, w106, w128, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w207, w233]]
def b8_14 : List (List Sig) := [[w38, w56, w106, w149, w182, w192, w233],
  [w38, w73, w106, w149, w182, w192, w233],
  [w38, w106, w112, w149, w182, w192, w233]]
def b8_15 : List (List Sig) := [[w14, w38, w106, w149, w182, w192, w233],
  [w33, w38, w106, w149, w182, w192, w233],
  [w34, w38, w106, w149, w182, w192, w233],
  [w38, w97, w106, w149, w182, w192, w233],
  [w38, w106, w149, w182, w192, w221, w233],
  [w38, w106, w149, w182, w192, w233, w254]]
def b8_16 : List (List Sig) := [[w10, w38, w106, w149, w182, w192, w233]]
def tier8 : List (List (List Sig)) := [b8_0, b8_1, b8_2, b8_3, b8_4, b8_5, b8_6, b8_7, b8_8, b8_9, b8_10, b8_11, b8_12, b8_13, b8_14, b8_15, b8_16]
def b9_9 : List (List Sig) := [[w38, w106, w149, w182, w192, w233]]
def tier9 : List (List (List Sig)) := [[], [], [], [], [], [], [], [], [], b9_9, [], [], [], [], [], [], []]
def buckets : ℕ → List (List (List Sig))
  | 1 => tier1
  | 2 => tier2
  | 3 => tier3
  | 4 => tier4
  | 5 => tier5
  | 6 => tier6
  | 7 => tier7
  | 8 => tier8
  | 9 => tier9
  | _ => []

def tiers (k : ℕ) := (buckets k).flatten
def lookup (k : ℕ) (w : List Sig) := bucketHas w (buckets k) (hashBucket w)
lemma lookup_sound (k : ℕ) (w : List Sig) (h : lookup k w = true) : w ∈ tiers k :=
  bucketHas_sound w (buckets k) (hashBucket w) h
end Minor6

namespace Minor0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level1 : checkRows 0 (lookup 0) (tiers 1) = true := by
  simp only [tiers,buckets,tier1,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level2 : checkRows 1 (lookup 1) (tiers 2) = true := by
  simp only [tiers,buckets,tier2,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level3 : checkRows 2 (lookup 2) (tiers 3) = true := by
  simp only [tiers,buckets,tier3,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level4 : checkRows 3 (lookup 3) (tiers 4) = true := by
  simp only [tiers,buckets,tier4,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_0 : checkRows 4 (lookup 4) b5_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_1 : checkRows 4 (lookup 4) b5_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_2 : checkRows 4 (lookup 4) b5_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_3 : checkRows 4 (lookup 4) b5_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_5 : checkRows 4 (lookup 4) b5_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_6 : checkRows 4 (lookup 4) b5_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_7 : checkRows 4 (lookup 4) b5_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_8 : checkRows 4 (lookup 4) b5_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_10 : checkRows 4 (lookup 4) b5_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_12 : checkRows 4 (lookup 4) b5_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_13 : checkRows 4 (lookup 4) b5_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_14 : checkRows 4 (lookup 4) b5_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b5_16 : checkRows 4 (lookup 4) b5_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level5 : checkRows 4 (lookup 4) (tiers 5) = true := by
  simp only [tiers,buckets,tier5,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b5_0, verify_b5_1, verify_b5_2, verify_b5_3, verify_b5_5, verify_b5_6, verify_b5_7, verify_b5_8, verify_b5_10, verify_b5_12, verify_b5_13, verify_b5_14, verify_b5_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_0 : checkRows 5 (lookup 5) b6_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_1 : checkRows 5 (lookup 5) b6_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_2 : checkRows 5 (lookup 5) b6_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_3 : checkRows 5 (lookup 5) b6_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_4 : checkRows 5 (lookup 5) b6_4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_5 : checkRows 5 (lookup 5) b6_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_6 : checkRows 5 (lookup 5) b6_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_7 : checkRows 5 (lookup 5) b6_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_8 : checkRows 5 (lookup 5) b6_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_9 : checkRows 5 (lookup 5) b6_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_10 : checkRows 5 (lookup 5) b6_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_11 : checkRows 5 (lookup 5) b6_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_12 : checkRows 5 (lookup 5) b6_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_13 : checkRows 5 (lookup 5) b6_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_14 : checkRows 5 (lookup 5) b6_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_15 : checkRows 5 (lookup 5) b6_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_16 : checkRows 5 (lookup 5) b6_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level6 : checkRows 5 (lookup 5) (tiers 6) = true := by
  simp only [tiers,buckets,tier6,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b6_0, verify_b6_1, verify_b6_2, verify_b6_3, verify_b6_4, verify_b6_5, verify_b6_6, verify_b6_7, verify_b6_8, verify_b6_9, verify_b6_10, verify_b6_11, verify_b6_12, verify_b6_13, verify_b6_14, verify_b6_15, verify_b6_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_0 : checkRows 6 (lookup 6) b7_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_1 : checkRows 6 (lookup 6) b7_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_2 : checkRows 6 (lookup 6) b7_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_3 : checkRows 6 (lookup 6) b7_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_4 : checkRows 6 (lookup 6) b7_4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_5 : checkRows 6 (lookup 6) b7_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_6 : checkRows 6 (lookup 6) b7_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_7 : checkRows 6 (lookup 6) b7_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_8 : checkRows 6 (lookup 6) b7_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_9 : checkRows 6 (lookup 6) b7_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_10 : checkRows 6 (lookup 6) b7_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_11 : checkRows 6 (lookup 6) b7_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_12 : checkRows 6 (lookup 6) b7_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_13 : checkRows 6 (lookup 6) b7_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_14 : checkRows 6 (lookup 6) b7_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_15 : checkRows 6 (lookup 6) b7_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_16 : checkRows 6 (lookup 6) b7_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level7 : checkRows 6 (lookup 6) (tiers 7) = true := by
  simp only [tiers,buckets,tier7,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b7_0, verify_b7_1, verify_b7_2, verify_b7_3, verify_b7_4, verify_b7_5, verify_b7_6, verify_b7_7, verify_b7_8, verify_b7_9, verify_b7_10, verify_b7_11, verify_b7_12, verify_b7_13, verify_b7_14, verify_b7_15, verify_b7_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_0 : checkRows 7 (lookup 7) b8_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_1 : checkRows 7 (lookup 7) b8_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_2 : checkRows 7 (lookup 7) b8_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_3 : checkRows 7 (lookup 7) b8_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_4 : checkRows 7 (lookup 7) b8_4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_5 : checkRows 7 (lookup 7) b8_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_6 : checkRows 7 (lookup 7) b8_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_7 : checkRows 7 (lookup 7) b8_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_8 : checkRows 7 (lookup 7) b8_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_9 : checkRows 7 (lookup 7) b8_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_10 : checkRows 7 (lookup 7) b8_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_11 : checkRows 7 (lookup 7) b8_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_12 : checkRows 7 (lookup 7) b8_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_13 : checkRows 7 (lookup 7) b8_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_14 : checkRows 7 (lookup 7) b8_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_15 : checkRows 7 (lookup 7) b8_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_16 : checkRows 7 (lookup 7) b8_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level8 : checkRows 7 (lookup 7) (tiers 8) = true := by
  simp only [tiers,buckets,tier8,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b8_0, verify_b8_1, verify_b8_2, verify_b8_3, verify_b8_4, verify_b8_5, verify_b8_6, verify_b8_7, verify_b8_8, verify_b8_9, verify_b8_10, verify_b8_11, verify_b8_12, verify_b8_13, verify_b8_14, verify_b8_15, verify_b8_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b9_15 : checkRows 8 (lookup 8) b9_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level9 : checkRows 8 (lookup 8) (tiers 9) = true := by
  simp only [tiers,buckets,tier9,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b9_15]

lemma v0 : verified tiers 0 := by simp [verified,tiers,buckets]
lemma v1 : verified tiers 1 := verificationStep (lookup_sound 0) v0 level1
lemma v2 : verified tiers 2 := verificationStep (lookup_sound 1) v1 level2
lemma v3 : verified tiers 3 := verificationStep (lookup_sound 2) v2 level3
lemma v4 : verified tiers 4 := verificationStep (lookup_sound 3) v3 level4
lemma v5 : verified tiers 5 := verificationStep (lookup_sound 4) v4 level5
lemma v6 : verified tiers 6 := verificationStep (lookup_sound 5) v5 level6
lemma v7 : verified tiers 7 := verificationStep (lookup_sound 6) v6 level7
lemma v8 : verified tiers 8 := verificationStep (lookup_sound 7) v7 level8
lemma v9 : verified tiers 9 := verificationStep (lookup_sound 8) v8 level9

lemma excluded (n : ℕ) (h : n ≤ 9) : ¬ BL n (minorRaw 0).toFinset := by
  have good : sortSignals (minorRaw 0) ∈ tiers 9 := by decide +kernel
  have nd : (minorRaw 0).Nodup := by decide +kernel
  intro live
  exact v9 _ good ((sorted_perm _).nodup_iff.mpr nd) n h ((sorted_set _).symm ▸ live)

end Minor0

namespace Minor6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level1 : checkRows 0 (lookup 0) (tiers 1) = true := by
  simp only [tiers,buckets,tier1,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level2 : checkRows 1 (lookup 1) (tiers 2) = true := by
  simp only [tiers,buckets,tier2,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level3 : checkRows 2 (lookup 2) (tiers 3) = true := by
  simp only [tiers,buckets,tier3,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level4 : checkRows 3 (lookup 3) (tiers 4) = true := by
  simp only [tiers,buckets,tier4,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level5 : checkRows 4 (lookup 4) (tiers 5) = true := by
  simp only [tiers,buckets,tier5,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_0 : checkRows 5 (lookup 5) b6_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_1 : checkRows 5 (lookup 5) b6_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_2 : checkRows 5 (lookup 5) b6_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_3 : checkRows 5 (lookup 5) b6_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_4 : checkRows 5 (lookup 5) b6_4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_5 : checkRows 5 (lookup 5) b6_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_6 : checkRows 5 (lookup 5) b6_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_7 : checkRows 5 (lookup 5) b6_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_8 : checkRows 5 (lookup 5) b6_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_9 : checkRows 5 (lookup 5) b6_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_10 : checkRows 5 (lookup 5) b6_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_11 : checkRows 5 (lookup 5) b6_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_12 : checkRows 5 (lookup 5) b6_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_13 : checkRows 5 (lookup 5) b6_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_14 : checkRows 5 (lookup 5) b6_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_15 : checkRows 5 (lookup 5) b6_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b6_16 : checkRows 5 (lookup 5) b6_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level6 : checkRows 5 (lookup 5) (tiers 6) = true := by
  simp only [tiers,buckets,tier6,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b6_0, verify_b6_1, verify_b6_2, verify_b6_3, verify_b6_4, verify_b6_5, verify_b6_6, verify_b6_7, verify_b6_8, verify_b6_9, verify_b6_10, verify_b6_11, verify_b6_12, verify_b6_13, verify_b6_14, verify_b6_15, verify_b6_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_0 : checkRows 6 (lookup 6) b7_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_1 : checkRows 6 (lookup 6) b7_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_2 : checkRows 6 (lookup 6) b7_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_3 : checkRows 6 (lookup 6) b7_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_4 : checkRows 6 (lookup 6) b7_4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_5 : checkRows 6 (lookup 6) b7_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_6 : checkRows 6 (lookup 6) b7_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_7 : checkRows 6 (lookup 6) b7_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_8 : checkRows 6 (lookup 6) b7_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_9 : checkRows 6 (lookup 6) b7_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_10 : checkRows 6 (lookup 6) b7_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_11 : checkRows 6 (lookup 6) b7_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_12 : checkRows 6 (lookup 6) b7_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_13 : checkRows 6 (lookup 6) b7_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_14 : checkRows 6 (lookup 6) b7_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_15 : checkRows 6 (lookup 6) b7_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b7_16 : checkRows 6 (lookup 6) b7_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level7 : checkRows 6 (lookup 6) (tiers 7) = true := by
  simp only [tiers,buckets,tier7,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b7_0, verify_b7_1, verify_b7_2, verify_b7_3, verify_b7_4, verify_b7_5, verify_b7_6, verify_b7_7, verify_b7_8, verify_b7_9, verify_b7_10, verify_b7_11, verify_b7_12, verify_b7_13, verify_b7_14, verify_b7_15, verify_b7_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_0 : checkRows 7 (lookup 7) b8_0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_1 : checkRows 7 (lookup 7) b8_1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_2 : checkRows 7 (lookup 7) b8_2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_3 : checkRows 7 (lookup 7) b8_3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_4 : checkRows 7 (lookup 7) b8_4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_5 : checkRows 7 (lookup 7) b8_5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_6 : checkRows 7 (lookup 7) b8_6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_7 : checkRows 7 (lookup 7) b8_7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_8 : checkRows 7 (lookup 7) b8_8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_9 : checkRows 7 (lookup 7) b8_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_10 : checkRows 7 (lookup 7) b8_10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_11 : checkRows 7 (lookup 7) b8_11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_12 : checkRows 7 (lookup 7) b8_12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_13 : checkRows 7 (lookup 7) b8_13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_14 : checkRows 7 (lookup 7) b8_14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_15 : checkRows 7 (lookup 7) b8_15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b8_16 : checkRows 7 (lookup 7) b8_16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level8 : checkRows 7 (lookup 7) (tiers 8) = true := by
  simp only [tiers,buckets,tier8,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b8_0, verify_b8_1, verify_b8_2, verify_b8_3, verify_b8_4, verify_b8_5, verify_b8_6, verify_b8_7, verify_b8_8, verify_b8_9, verify_b8_10, verify_b8_11, verify_b8_12, verify_b8_13, verify_b8_14, verify_b8_15, verify_b8_16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verify_b9_9 : checkRows 8 (lookup 8) b9_9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma level9 : checkRows 8 (lookup 8) (tiers 9) = true := by
  simp only [tiers,buckets,tier9,checkRows_flatten,checkRows_nil,List.all_cons,List.all_nil,
    Bool.and_self,Bool.true_and, verify_b9_9]

lemma v0 : verified tiers 0 := by simp [verified,tiers,buckets]
lemma v1 : verified tiers 1 := verificationStep (lookup_sound 0) v0 level1
lemma v2 : verified tiers 2 := verificationStep (lookup_sound 1) v1 level2
lemma v3 : verified tiers 3 := verificationStep (lookup_sound 2) v2 level3
lemma v4 : verified tiers 4 := verificationStep (lookup_sound 3) v3 level4
lemma v5 : verified tiers 5 := verificationStep (lookup_sound 4) v4 level5
lemma v6 : verified tiers 6 := verificationStep (lookup_sound 5) v5 level6
lemma v7 : verified tiers 7 := verificationStep (lookup_sound 6) v6 level7
lemma v8 : verified tiers 8 := verificationStep (lookup_sound 7) v7 level8
lemma v9 : verified tiers 9 := verificationStep (lookup_sound 8) v8 level9

lemma excluded (n : ℕ) (h : n ≤ 9) : ¬ BL n (minorRaw 6).toFinset := by
  have good : sortSignals (minorRaw 6) ∈ tiers 9 := by decide +kernel
  have nd : (minorRaw 6).Nodup := by decide +kernel
  intro live
  exact v9 _ good ((sorted_perm _).nodup_iff.mpr nd) n h ((sorted_set _).symm ▸ live)

end Minor6

lemma all_minors (i : Fin 7) (n : ℕ) (h : n ≤ 9) : ¬ BL n (minorRaw i).toFinset := by
  intro live
  have moved := representative_eq i ▸ live
  by_cases e : i = 6
  · have same : representative i = 6 := if_pos e
    rw [same] at moved
    exact Minor6.excluded n h moved
  · have same : representative i = 0 := if_neg e
    rw [same] at moved
    exact Minor0.excluded n h moved

end PEqualNP.Outside.L_meta_10478

namespace PEqualNP.Outside.L_meta_10478

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Basis1868 Free1868 FreeSearch1868 Check2516

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [13, 16]⟩, ⟨.and, [14, 10]⟩, ⟨.or, [17, 18]⟩], 19⟩

lemma witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

lemma witness_size : witness.size = 13 := rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma witness_eval : ∀ x : Fin 7 → Bool, witness.eval (List.ofFn x) = edge x := by
  decide +kernel

def flatEdges : List ℕ :=
  [0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6]

def tableEdge (x : Fin 7 → Bool) : Bool := decide (∃ i < flatEdges.length / 2,
  (List.ofFn x).getD (flatEdges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (flatEdges.getD (2*i+1) 0) false = true)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma table_match : ∀ x, tableEdge x = edge x := by decide +kernel

lemma replacement
    (excluded : ∀ (i : Fin 7) (l : ℕ), l ≤ 9 → ¬ BL l (minorRaw i).toFinset)
    (gates : List Gate) (o : ℕ) (legal : FanInTwo (⟨gates,o⟩ : Circuit))
    (spec : ∀ x, (⟨gates,o⟩ : Circuit).eval (List.ofFn x) = tableEdge x) :
    ∃ (gs' : List Gate) (o' : ℕ),
      (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gates.length ∧
      ∀ x, (⟨gs',o'⟩ : Circuit).eval (List.ofFn x) = tableEdge x := by
  by_cases hasNot : ∃ g ∈ gates, g.op = .not
  · have lower := conditional_binary_lower excluded ⟨gates,o⟩ legal
      (fun x => (spec x).trans (table_match x))
    change 12 ≤ gates.countP costly at lower
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

end PEqualNP.Outside.L_meta_10478

theorem PEqualNP.Outside.L_meta_10478 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ spec
  exact PEqualNP.Outside.L_meta_10478.replacement PEqualNP.Outside.L_meta_10478.all_minors gates o
    (fun g hg => legal g hg) spec
