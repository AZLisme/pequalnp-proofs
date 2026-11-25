import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9454.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit simplifier is adapted from L_meta_7328 and L_meta_1411
-- in open-goat/pequalnp-proofs under the Apache 2.0 license.
abbrev Stat := Bool ⊕ ℕ

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma op_cases {g : Gate} (h : Good g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa using h.1

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Good g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Good]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Good]
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Good g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op (op_cases hgok) w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

-- Every gate with a constant input can be omitted. An absorbing input
-- additionally marks the gate output as a constant for the next gate.
def absorb : GateOp → Bool
  | .or => true
  | _ => false

lemma simplify_drop (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : ∃ b, Sum.inl b ∈ ins) :
    (simplify op m ins).1 = none := by
  rcases hc with ⟨b, hb⟩
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hb hl
  all_goals cases s <;> (try cases t) <;> simp_all [simplify, simpAnd, simpOr]

lemma simplify_absorb (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (ins : List Stat) (hl : ins.length ≤ 2)
    (hc : Sum.inl (absorb op) ∈ ins) :
    (simplify op m ins).2 = Sum.inl (absorb op) := by
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨s, _ | ⟨t, _ | ⟨u, us⟩⟩⟩
  all_goals simp at hc hl
  all_goals cases s <;> (try cases t) <;> simp_all [absorb, simplify, simpAnd, simpOr]
  grind

abbrev State := List Stat × List Gate

def stat (s : State) (i : ℕ) : Stat := s.1.getD i (Sum.inl false)

def plan (n : ℕ) (s : State) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + s.2.length) (g.inputs.map (stat s))

lemma elim_append (n : ℕ) (pre post : List Gate) (s : State) :
    elim n (pre ++ post) s = elim n post (elim n pre s) := by
  simp [elim, List.foldl_append]

lemma elim_extends (n : ℕ) (gs : List Gate) (s : State) :
    ∃ t, (elim n gs s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (elimStep n s g)
    refine ⟨(plan n s g).2 :: t, ?_, by simp [hlen]⟩
    change (elim n gs (elimStep n s g)).1 = _
    rw [ht]
    change (s.1 ++ [(plan n s g).2]) ++ t = _
    simp

lemma elim_stat (n : ℕ) (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    stat (elim n gs s) i = stat s i := by
  obtain ⟨t, ht, _⟩ := elim_extends n gs s
  unfold stat
  rw [ht, List.getD_append _ _ _ _ hi]

lemma elim_good (n : ℕ) (gs : List Gate) (s : State)
    (h : ∀ g ∈ gs, Good g) (hs : ∀ g ∈ s.2, Good g) :
    ∀ g ∈ (elim n gs s).2, Good g := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    change ∀ g' ∈ (elim n gs (elimStep n s g)).2, Good g'
    apply ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    intro a ha
    change a ∈ s.2 ++ (plan n s g).1.toList at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hs a ha
    · exact simplify_ok _ _ _ a (by simpa [plan] using ha)

def fix {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i = p then b else x i

def initial {n : ℕ} (p : Fin n) (b : Bool) : State :=
  (List.ofFn fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val, [])

lemma initial_length {n : ℕ} (p : Fin n) (b : Bool) :
    (initial p b).1.length = n := by simp [initial]

lemma initial_stat {n : ℕ} (p : Fin n) (b : Bool) : stat (initial p b) p.val = Sum.inl b := by
  simp [stat, initial]

lemma initial_inv {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (fix p b x)) (initial p b) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (stat (initial p b) j.val).Valid _ ∧ (stat (initial p b) j.val).val _ = _
    by_cases hj : j = p <;>
      simp [stat, initial, fix, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at *
  · rw [List.getD_eq_default _ _ (by simpa [initial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma drop_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} {b : Bool} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl b) :
    (plan n s g).1 = none := by
  apply simplify_drop _ (op_cases hg) _ _ (by simpa using hg.2)
  exact ⟨b, hb ▸ List.mem_map_of_mem hi⟩

lemma absorb_at_reader (n : ℕ) (s : State) (g : Gate) (hg : Good g)
    {i : ℕ} (hi : i ∈ g.inputs) (hb : stat s i = Sum.inl (absorb g.op)) :
    (plan n s g).2 = Sum.inl (absorb g.op) := by
  apply simplify_absorb _ (op_cases hg) _ _ (by simpa using hg.2)
  exact hb ▸ List.mem_map_of_mem hi

lemma restriction (C : Circuit) (hm : Monotone2 C) {n : ℕ} (p : Fin n) (b : Bool)
    (hnc : ∃ x y, circuitFun n C (fix p b x) ≠ circuitFun n C (fix p b y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧
      D.size = (elim n C.gates (initial p b)).2.length := by
  let s := elim n C.gates (initial p b)
  have hval (x : Fin n → Bool) :
      (stat s C.output).val (wiresFrom s.2 (List.ofFn x)) =
        circuitFun n C (fix p b x) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ hm (initial_inv p b x)).2 C.output).2
  cases hz : stat s C.output with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x
    have hy := hval y
    rw [hz] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨s.2, j⟩, elim_good n _ _ hm (by simp [initial]), ?_, rfl⟩
    intro x
    change (wiresFrom s.2 (List.ofFn x)).getD j false = _
    simpa only [hz, Stat.val] using hval x

lemma single_drop {n : ℕ} (p : Fin n) (b : Bool) (pre post : List Gate) (g : Gate)
    (hg : Good g) (hp : p.val ∈ g.inputs) :
    (elim n (pre ++ g :: post) (initial p b)).2.length + 1 ≤
      (pre ++ g :: post).length := by
  let s := elim n pre (initial p b)
  have hs : stat s p.val = Sum.inl b :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p b)
  have hd := drop_at_reader n s g hg hp hs
  have hpre := elim_len n pre (initial p b)
  have hpost := elim_len n post (elimStep n s g)
  rw [elim_append]
  change (elim n post (elimStep n s g)).2.length + 1 ≤ _
  have hstep : (elimStep n s g).2.length = s.2.length := by
    change (s.2 ++ (plan n s g).1.toList).length = _
    simp [hd]
  rw [hstep] at hpost
  change s.2.length ≤ 0 + pre.length at hpre
  simp only [List.length_append, List.length_cons]
  omega

lemma double_drop {n : ℕ} (p : Fin n) (pre mid post : List Gate) (g h : Gate)
    (hg : Good g) (hh : Good h) (hp : p.val ∈ g.inputs) (hr : n + pre.length ∈ h.inputs) :
    (elim n (pre ++ g :: (mid ++ h :: post)) (initial p (absorb g.op))).2.length + 2 ≤
      (pre ++ g :: (mid ++ h :: post)).length := by
  let s := elim n pre (initial p (absorb g.op))
  let t := elimStep n s g
  let u := elim n mid t
  have hs : stat s p.val = Sum.inl (absorb g.op) :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p _)
  have hd := drop_at_reader n s g hg hp hs
  have hc := absorb_at_reader n s g hg hp hs
  obtain ⟨suffix, hext, hlen⟩ := elim_extends n pre (initial p (absorb g.op))
  have hl : s.1.length = n + pre.length := by
    change (elim n pre (initial p (absorb g.op))).1.length = _
    rw [hext, List.length_append, initial_length, hlen]
  have ht : stat t (n + pre.length) = Sum.inl (absorb g.op) := by
    change (s.1 ++ [(plan n s g).2]).getD (n + pre.length) _ = _
    rw [getD_snoc_len _ _ _ _ hl, hc]
  have hlt : n + pre.length < t.1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [hl]
  have hu := (elim_stat n mid t _ hlt).trans ht
  have hd' := drop_at_reader n u h hh hr hu
  have hpre := elim_len n pre (initial p (absorb g.op))
  have hmid := elim_len n mid t
  have hpost := elim_len n post (elimStep n u h)
  have hstep : t.2.length = s.2.length := by
    change (s.2 ++ (plan n s g).1.toList).length = _
    simp [hd]
  have hstep' : (elimStep n u h).2.length = u.2.length := by
    change (u.2 ++ (plan n u h).1.toList).length = _
    simp [hd']
  rw [hstep] at hmid
  rw [hstep'] at hpost
  change s.2.length ≤ 0 + pre.length at hpre
  change u.2.length ≤ _ at hmid
  rw [elim_append]
  change (elim n (mid ++ h :: post) t).2.length + 2 ≤ _
  rw [elim_append]
  change (elim n post (elimStep n u h)).2.length + 2 ≤ _
  simp only [List.length_append, List.length_cons]
  omega

-- A dependency trace either reaches a direct reader or contains two successive gates.
def Direct (n p w : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre post : List Gate) (g : Gate),
    gs = pre ++ g :: post ∧ p ∈ g.inputs ∧ w = n + pre.length

def Chain (n p : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre mid post : List Gate) (g h : Gate),
    gs = pre ++ g :: (mid ++ h :: post) ∧ p ∈ g.inputs ∧ n + pre.length ∈ h.inputs

lemma wire_trace {n p : ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ w, w ≠ p → x.getD w false = y.getD w false)
    (gs : List Gate) (w : ℕ)
    (hne : (wiresFrom gs x).getD w false ≠ (wiresFrom gs y).getD w false) :
    w = p ∨ Direct n p w gs ∨ Chain n p gs := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    exact Or.inl (by by_contra h; exact hne (hxy w h))
  | append_singleton gs g ih =>
    have hxlen : (wiresFrom gs x).length = n + gs.length := by rw [length_wiresFrom, hx]
    have hylen : (wiresFrom gs y).length = n + gs.length := by rw [length_wiresFrom, hy]
    rw [wiresFrom_append, wiresFrom_append] at hne
    change ((wiresFrom gs x) ++ [_]).getD w false ≠
      ((wiresFrom gs y) ++ [_]).getD w false at hne
    by_cases hw : w = n + gs.length
    · rw [getD_snoc_len _ _ _ _ (hxlen.trans hw.symm),
          getD_snoc_len _ _ _ _ (hylen.trans hw.symm)] at hne
      obtain ⟨i, hi, hdiff⟩ : ∃ i ∈ g.inputs,
          (wiresFrom gs x).getD i false ≠ (wiresFrom gs y).getD i false := by
        by_contra! hsame
        apply hne
        apply congrArg (GateOp.eval g.op)
        exact List.map_congr_left hsame
      rcases ih i hdiff with rfl | ⟨pre, post, h, he, hr, rfl⟩ | ⟨pre, mid, post, h, k, he, hr, hs⟩
      · exact Or.inr (Or.inl ⟨gs, [], g, rfl, hi, hw⟩)
      · exact Or.inr (Or.inr ⟨pre, post, [], h, g, by simp [he, List.append_assoc], hr, hi⟩)
      · exact Or.inr (Or.inr ⟨pre, mid, post ++ [g], h, k,
          by simp [he, List.append_assoc], hr, hs⟩)
    · rw [getD_snoc_ne _ _ _ _ (by rwa [hxlen]), getD_snoc_ne _ _ _ _ (by rwa [hylen])] at hne
      rcases ih w hne with hp | ⟨pre, post, h, he, hr, hval⟩ | ⟨pre, mid, post, h, k, he, hr, hs⟩
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨pre, post ++ [g], h, by simp [he, List.append_assoc], hr, hval⟩)
      · exact Or.inr (Or.inr ⟨pre, mid, post ++ [g], h, k,
          by simp [he, List.append_assoc], hr, hs⟩)

lemma fix_agree {n : ℕ} (p : Fin n) (x : Fin n → Bool) (w : ℕ) (hw : w ≠ p.val) :
    (List.ofFn (fix p false x)).getD w false =
      (List.ofFn (fix p true x)).getD w false := by
  by_cases hi : w < n
  · let i : Fin n := ⟨w, hi⟩
    have hn : i ≠ p := fun h => hw (congrArg Fin.val h)
    change (List.ofFn (fix p false x)).getD i.val false =
      (List.ofFn (fix p true x)).getD i.val false
    simp [fix, hn]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

def Nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

def Essential {n : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) : Prop :=
  ∃ x, f (fix p false x) ≠ f (fix p true x)

lemma trace_of_essential {n : ℕ} (C : Circuit) (p : Fin n)
    (he : Essential (circuitFun n C) p)
    (hnc : Nonconstant (fun x => circuitFun n C (fix p false x))) :
    Direct n p.val C.output C.gates ∨ Chain n p.val C.gates := by
  obtain ⟨x, hx⟩ := he
  rcases wire_trace (n := n) (x := List.ofFn (fix p false x)) (y := List.ofFn (fix p true x))
      (by simp) (by simp) (fix_agree p x) C.gates C.output hx with hp | h
  · exfalso
    obtain ⟨v, w, hne⟩ := hnc
    apply hne
    have heval (z : Fin n → Bool) : circuitFun n C (fix p false z) = false := by
      change (wiresFrom C.gates (List.ofFn (fix p false z))).getD C.output false = false
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn (fix p false z))
      rw [hp, ht, List.getD_append _ _ _ _ (by simp)]
      simp [fix]
    change circuitFun n C (fix p false v) = circuitFun n C (fix p false w)
    rw [heval v, heval w]
  · exact h

lemma direct_const {n : ℕ} (p : Fin n) (pre post : List Gate) (g : Gate)
    (hm : ∀ h ∈ pre ++ g :: post, Good h) (hp : p.val ∈ g.inputs) (x : Fin n → Bool) :
    circuitFun n ⟨pre ++ g :: post, n + pre.length⟩ (fix p (absorb g.op) x) = absorb g.op := by
  let s := elim n pre (initial p (absorb g.op))
  let t := elimStep n s g
  have hg : Good g := hm g (by simp)
  have hs : stat s p.val = Sum.inl (absorb g.op) :=
    (elim_stat n pre _ _ (by rw [initial_length]; exact p.isLt)).trans (initial_stat p _)
  have hc := absorb_at_reader n s g hg hp hs
  obtain ⟨suffix, hext, hlen⟩ := elim_extends n pre (initial p (absorb g.op))
  have hl : s.1.length = n + pre.length := by
    change (elim n pre (initial p (absorb g.op))).1.length = _
    rw [hext, List.length_append, initial_length, hlen]
  have ht : stat t (n + pre.length) = Sum.inl (absorb g.op) := by
    change (s.1 ++ [(plan n s g).2]).getD (n + pre.length) _ = _
    rw [getD_snoc_len _ _ _ _ hl, hc]
  have hlt : n + pre.length < t.1.length := by
    change _ < (s.1 ++ [(plan n s g).2]).length
    simp [hl]
  have hstat : stat (elim n (pre ++ g :: post) (initial p (absorb g.op))) (n + pre.length) =
      Sum.inl (absorb g.op) := by
    rw [elim_append]
    exact (elim_stat n post t _ hlt).trans ht
  have hval := ((inv_elim n _ (by simp) _ _ _ hm (initial_inv p (absorb g.op) x)).2
    (n + pre.length)).2
  change (stat (elim n (pre ++ g :: post) (initial p (absorb g.op))) (n + pre.length)).val _ = _ at hval
  rw [hstat] at hval
  exact hval.symm

lemma leaf_step {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p : Fin n)
    (he : Essential (circuitFun n C) p)
    (hnc : ∀ b, Nonconstant (fun x => circuitFun n C (fix p b x))) :
    ∃ (b : Bool) (D : Circuit), Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p b x)) ∧ D.size + 2 ≤ C.size := by
  rcases trace_of_essential C p he (hnc false) with hd | ⟨pre, mid, post, g, h, hgs, hp, hr⟩
  · rcases C with ⟨gs, out⟩
    obtain ⟨pre, post, g, rfl, hp, rfl⟩ := hd
    obtain ⟨x, y, hxy⟩ := hnc (absorb g.op)
    exact False.elim (hxy ((direct_const p pre post g hm hp x).trans
      (direct_const p pre post g hm hp y).symm))
  · obtain ⟨D, hD, hval, hsz⟩ := restriction C hm p (absorb g.op) (hnc _)
    refine ⟨absorb g.op, D, hD, hval, ?_⟩
    have hg : Good g := hm g (by simp [hgs])
    have hh : Good h := hm h (by simp [hgs])
    rw [hsz, Circuit.size, hgs]
    exact double_drop p pre mid post g h hg hh hp hr

lemma center_step {n : ℕ} (C : Circuit) (hm : Monotone2 C) (p : Fin n)
    (hnc : Nonconstant (fun x => circuitFun n C (fix p false x))) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun n C (fix p false x)) ∧
      D.size ≤ C.size ∧ (Essential (circuitFun n C) p → D.size + 1 ≤ C.size) := by
  obtain ⟨D, hD, hval, hsz⟩ := restriction C hm p false hnc
  refine ⟨D, hD, hval, ?_, ?_⟩
  · rw [hsz, Circuit.size]
    simpa [initial] using elim_len n C.gates (initial p false)
  · intro he
    rw [hsz, Circuit.size]
    have hr : ∃ pre post g, C.gates = pre ++ g :: post ∧ p.val ∈ g.inputs := by
      rcases trace_of_essential C p he hnc with ⟨pre, post, g, hh, hg, _⟩ |
        ⟨pre, mid, post, g, h, hh, hg, _⟩
      · exact ⟨pre, post, g, hh, hg⟩
      · exact ⟨pre, mid ++ h :: post, g, hh, hg⟩
    obtain ⟨pre, post, g, hh, hg⟩ := hr
    have hg' := hm g (by simp [hh])
    rw [hh]
    exact single_drop p false pre post g hg' hg

def q5step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def q5R (a b : Bool) : Prop := a = true → b = true

theorem q5_getD {w w' : List Bool} (h : List.Forall₂ q5R w w') :
    ∀ i, w.getD i false = true → w'.getD i false = true := by
  induction h with
  | nil => intro i h; simp at h
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa [q5R] using hab
    | succ i => simpa using ih i

theorem q5_step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ q5R w w') : List.Forall₂ q5R (q5step w g) (q5step w' g) := by
  unfold q5step
  refine List.rel_append h (List.Forall₂.cons ?_ List.Forall₂.nil)
  have hr := q5_getD h
  unfold q5R
  rcases hg with hg | hg <;> rw [hg] <;>
    simp only [GateOp.eval, List.all_map, List.any_map, List.all_eq_true, List.any_eq_true,
      Function.comp_apply, id]
  · intro H i hi; exact hr i (H i hi)
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, hr i h⟩

theorem q5_fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ {w w' : List Bool}, List.Forall₂ q5R w w' →
      List.Forall₂ q5R (gs.foldl q5step w) (gs.foldl q5step w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    exact ih (fun g' hg' => hg g' (by simp [hg'])) (q5_step_mono g (hg g (by simp)) h)

theorem q5_eval_mono {n : ℕ} (C : Circuit) (hC : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ k, x k = true → y k = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have h0 : List.Forall₂ q5R (List.ofFn x) (List.ofFn y) := by
    rw [List.ofFn_eq_map, List.ofFn_eq_map, List.forall₂_map_left_iff,
      List.forall₂_map_right_iff, List.forall₂_same]
    intro k _
    exact hxy k
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgm
    have := (hC g hgm).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have h1 := q5_fold_mono C.gates hg h0
  exact q5_getD h1 C.output


-- Restriction and monotonicity follow the checked proofs L_meta_7961 and L_meta_3005.
abbrev Sample := Fin 5 × Fin 5

def sample (e : Sample) (k : Fin 10) : Bool :=
  decide (k.val = e.1.val ∨ k.val = 5 + e.2.val)

set_option maxRecDepth 8192 in
lemma sample_eq : ∀ u v : Fin 5, List.ofFn (sample (u,v)) = PEqualNP.Represents.oneEach u v := by
  decide +kernel

def mat (e : Sample) : Bool :=
  (7577398 : ℕ).testBit (5 * e.1.val + e.2.val)

abbrev allowed (d : List (Fin 10)) (e : Sample) : Prop :=
  ∀ p ∈ d, sample e p = false

def agrees (C : Circuit) (d : List (Fin 10)) : Prop :=
  ∀ e : Sample, allowed d e → circuitFun 10 C (sample e) = mat e

lemma fix_keeps (p : Fin 10) (x : Fin 10 → Bool) (b : Bool) (h : x p = b) :
    fix p b x = x := by
  funext i
  by_cases e : i = p
  · subst i
    simp [fix, h]
  · simp [fix, e]

lemma project_one (C : Circuit) (hm : Monotone2 C) (d : List (Fin 10)) (h : agrees C d)
    (p : Fin 10) (pos neg good bad : Sample)
    (posAllowed : allowed d pos) (negAllowed : allowed d neg)
    (posVal : mat pos = true) (negVal : mat neg = false) (posOn : sample pos p = true)
    (negDominates : ∀ k, fix p false (sample pos) k = true → sample neg k = true)
    (goodAllowed : allowed (p::d) good) (badAllowed : allowed (p::d) bad)
    (goodVal : mat good = true) (badVal : mat bad = false) :
    ∃ D : Circuit, Monotone2 D ∧ agrees D (p::d) ∧ D.size + 1 ≤ C.size := by
  have no : circuitFun 10 C (fix p false (sample pos)) = false := by
    by_contra hx
    have ht : circuitFun 10 C (fix p false (sample pos)) = true := by
      cases hq : circuitFun 10 C (fix p false (sample pos)) <;> simp_all
    have hneg := q5_eval_mono C hm _ _ negDominates ht
    change circuitFun 10 C (sample neg) = true at hneg
    rw [h neg negAllowed, negVal] at hneg
    contradiction
  have yes : circuitFun 10 C (fix p true (sample pos)) = true := by
    rw [fix_keeps _ _ _ posOn, h pos posAllowed, posVal]
  have nonconstant : Nonconstant (fun x => circuitFun 10 C (fix p false x)) := by
    refine ⟨sample good, sample bad, ?_⟩
    dsimp only
    rw [fix_keeps _ _ _ (goodAllowed p List.mem_cons_self),
      fix_keeps _ _ _ (badAllowed p List.mem_cons_self)]
    have hgood : allowed d good := fun i hi => goodAllowed i (List.mem_cons_of_mem _ hi)
    have hbad : allowed d bad := fun i hi => badAllowed i (List.mem_cons_of_mem _ hi)
    rw [h good hgood, h bad hbad, goodVal, badVal]
    decide
  obtain ⟨D, hd, eval, _, save⟩ := center_step C hm p nonconstant
  have essential : Essential (circuitFun 10 C) p := by
    exact ⟨sample pos, by rw [no,yes]; decide⟩
  refine ⟨D, hd, ?_, save essential⟩
  intro e he
  rw [eval, fix_keeps _ _ _ (he p List.mem_cons_self)]
  exact h e (fun i hi => he i (List.mem_cons_of_mem _ hi))

set_option maxRecDepth 8192 in
lemma projection (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents (fun u v : Fin 5 =>
      (7577398 : ℕ).testBit (5 * u.val + v.val)) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 7 ∧
      ∀ u v : Fin 5, u.val < 3 → v ≠ 2 →
        D.eval (PEqualNP.Represents.oneEach u v) = mat (u,v) := by
  have base : agrees C [] := by
    rintro ⟨u,v⟩ _
    change C.eval (List.ofFn (sample (u,v))) = mat (u,v)
    rw [sample_eq]
    exact hr u v
  obtain ⟨D, hd, hD, sD⟩ := project_one C hm [] base 3 (3,0) (0,0) (0,1) (0,0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨E, he, hE, sE⟩ := project_one D hd [3] hD 4 (4,0) (0,0) (0,1) (0,0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨F, hf, hF, sF⟩ := project_one E he [4,3] hE 7 (0,2) (0,0) (0,1) (0,0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have leftover : ∀ u v : Fin 5, u.val < 3 → v ≠ 2 → allowed [7,4,3] (u,v) := by
    decide +kernel
  refine ⟨F, hf, by omega, ?_⟩
  intro u v hu hv
  simpa only [circuitFun, sample_eq] using hF (u,v) (leftover u v hu hv)

end PEqualNP.Outside.L_meta_9454.Restriction


-- The live-set search and its completeness proof are adapted from
-- the checked proof L_meta_8299. The input table and computation are specific to this graph.

namespace PEqualNP.Outside.L_meta_9454

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 70

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 35 := ((x >>> 35) &&& ~~~x).setWidth 35

def cuts (ws : List W) : BitVec 35 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 35) ++ (0 : BitVec 35)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x1ff8c6318c63, 0xfffe00108421084, 0x3ff0000006318c6318, 0x0, 0x0, 0x1f003e00042108421, 0x3e000000f908421084, 0x0, 0x7c000294a5294a, 0xf801f0421084210]

def inputs : List W := rawInputs.filter (fun w => w != 0)

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 35) (w : W) : Prop :=
  w.getLsbD (35 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 35) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (35 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (35 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 35, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 35) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 70 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 35)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 70 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 70) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 70) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 70, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 70 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 70 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 70 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 70 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 70) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 70 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 5 → Fin 5 → Bool := fun u v => (7577398 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 5 × Fin 5) := [(0, 1), (0, 4), (1, 0), (1, 3), (1, 4), (2, 0), (2, 1)]
def negL : List (Fin 5 × Fin 5) := [(0, 0), (0, 3), (1, 1), (2, 3), (2, 4)]

def samp (k : Fin 70) : Fin 5 × Fin 5 :=
  if k.val < 35 then negL.getD (k.val % 5) (0, 0)
  else posL.getD ((k.val - 35) / 5) (0, 0)

def KeptCells (C : Circuit) : Prop :=
  ∀ (u v : Fin 5), u.val < 3 → v ≠ 2 → C.eval (PEqualNP.Represents.oneEach u v) = A u v

theorem samp_kept : ∀ k : Fin 70, (samp k).1.val < 3 ∧ (samp k).2 ≠ 2 := by
  decide +kernel

theorem input_rows : ∀ k : Fin 70,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 70, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : KeptCells C) (k : Fin 70) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2 (samp_kept k).1 (samp_kept k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  by_cases h : u = 0
  · exact .inl h
  · exact .inr (.inr (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hu, by simpa using h⟩)))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : KeptCells C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

theorem inputs_length : inputs.length = 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem front_small : (inputs.sublists.filter (fun l => decide (l.length < 7))).all
    (fun l => !(cuts l == -1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_none : optimized 7 1 inputs = false := by decide +kernel

theorem no_small_restricted (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 7)
    (hr : KeptCells C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 7 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 7 l (8 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hsl : l.Sublist inputs := List.filter_sublist
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr hsl
  by_cases hlen : l.length < 7
  · have hrow := List.all_eq_true.mp front_small l
      (List.mem_filter.mpr ⟨hmem, by simpa using hlen⟩)
    have hcuts := cuts_full (hlS ▸ hl3 : live basicOps goal 7 l.toFinset)
    simp [hcuts] at hrow
  · have hle := hsl.length_le
    rw [inputs_length] at hle
    have heq : l = inputs := hsl.eq_of_length (by rw [inputs_length]; omega)
    rw [heq, inputs_length] at hsearch
    have hf : optimized 7 1 inputs = false := full_none
    have h1 : (8 - 7 : ℕ) = 1 := rfl
    rw [h1, hf] at hsearch
    exact Bool.noConfusion hsearch

end PEqualNP.Outside.L_meta_9454


theorem PEqualNP.Outside.L_meta_9454 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7577398 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨D, hd, ht, hk⟩ := PEqualNP.Outside.L_meta_9454.Restriction.projection C hm hs hr
  exact PEqualNP.Outside.L_meta_9454.no_small_restricted D hd ht hk
