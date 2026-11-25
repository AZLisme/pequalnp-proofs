import PEqualNP.Defs

-- The live-set search and completeness proof are adapted from L-meta-8299.

namespace PEqualNP.Outside.L_meta_9460

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

section Projection

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def zeroCount (f : α → β) (zero : β) (s : Finset α) : Nat :=
  (s.filter (fun w => f w = zero)).card

def projected (f : α → β) (zero : β) (s : Finset α) : Finset β :=
  (s.image f).erase zero

lemma projected_insert (f : α → β) (zero : β) (a : α) (s : Finset α) :
    projected f zero (insert a s) =
    if f a = zero then projected f zero s else insert (f a) (projected f zero s) := by
  by_cases h : f a = zero
  · simp [projected, Finset.image_insert, h, Finset.erase_insert_eq_erase]
  · simp [projected, Finset.image_insert, h, Finset.erase_insert_of_ne h]

lemma zeroCount_insert_le (f : α → β) (zero : β) (a : α) (s : Finset α) :
    zeroCount f zero (insert a s) ≤ zeroCount f zero s + (if f a = zero then 1 else 0) := by
  by_cases h : f a = zero
  · simpa [zeroCount, Finset.filter_insert, h] using
      Finset.card_insert_le a (s.filter (fun w => f w = zero))
  · simp [zeroCount, Finset.filter_insert, h]

lemma zeroCount_insert (f : α → β) (zero : β) (a : α) (s : Finset α) (h : a ∉ s) :
    zeroCount f zero (insert a s) = zeroCount f zero s + (if f a = zero then 1 else 0) := by
  by_cases he : f a = zero
  · have hn : a ∉ s.filter (fun w => f w = zero) := by simp [Finset.mem_filter, h]
    simp [zeroCount, Finset.filter_insert, he, Finset.card_insert_of_notMem hn]
  · simp [zeroCount, Finset.filter_insert, he]

lemma build_mono_set {ops : β → β → Finset β} {goal : β} {k : Nat}
    {s t : Finset β} (h : build ops goal k s) (sub : s ⊆ t) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact sub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact .inl (ih skip sub)
    · exact .inr ⟨a, sub ha, b, sub hb, hab, z, hz, ih tail (Finset.insert_subset_insert z sub)⟩

lemma build_mono_budget {ops : β → β → Finset β} {goal : β} {k l : Nat}
    {s : Finset β} (h : build ops goal k s) (le : k ≤ l) : build ops goal l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

lemma project_with_saving (f : α → β) (zero : β)
    (op : α → α → Finset α) (op' : β → β → Finset β) (target : α)
    (hgoal : f target ≠ zero)
    (hom : ∀ a b z, z ∈ op a b → f z ∈ op' (f a) (f b))
    (leftZero : ∀ b z, z ∈ op' zero b → z = zero ∨ z = b)
    (rightZero : ∀ a z, z ∈ op' a zero → z = zero ∨ z = a)
    (same : ∀ a z, z ∈ op' a a → z = a)
    {k : Nat} {s : Finset α} (h : live op target k s) :
    build op' (f target) (k - zeroCount f zero s) (projected f zero s) := by
  induction k generalizing s with
  | zero =>
    change s = {target} at h
    subst s
    simp [projected, zeroCount, hgoal, build]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, rfl, tail⟩
    · exact build_mono_budget (ih skip) (by omega)
    · have hzr : z ∉ rest := by
        intro h
        exact hzout (by simp [h])
      have current := ih tail
      have gate := hom a b z hz
      have cRest : zeroCount f zero rest ≤ zeroCount f zero (insert z rest) := by
        rw [zeroCount_insert _ _ _ _ hzr]
        omega
      have cb := zeroCount_insert_le f zero b rest
      have ca := zeroCount_insert_le f zero a (insert b rest)
      have wz (p : f z = zero ∨ f z = f a ∨ f z = f b) :
          projected f zero (insert z rest) ⊆
            projected f zero (insert a (insert b rest)) := by
        rw [projected_insert, projected_insert, projected_insert]
        rcases p with hz | eqa | eqb
        · by_cases ha : f a = zero <;> by_cases hb : f b = zero <;> simp [hz, ha, hb, Finset.subset_iff, Finset.mem_insert] <;> tauto
        · by_cases ha : f a = zero <;> by_cases hb : f b = zero <;> simp [eqa, ha, hb, Finset.subset_iff, Finset.mem_insert] <;> tauto
        · by_cases ha : f a = zero <;> by_cases hb : f b = zero <;> simp [eqb, ha, hb, Finset.subset_iff, Finset.mem_insert] <;> tauto
      have noCost (hle : zeroCount f zero (insert a (insert b rest)) ≤
            zeroCount f zero (insert z rest) + 1)
          (p : f z = zero ∨ f z = f a ∨ f z = f b) :
          build op' (f target) (k+1 - zeroCount f zero (insert a (insert b rest)))
            (projected f zero (insert a (insert b rest))) :=
        build_mono_budget (build_mono_set current (wz p)) (by omega)
      by_cases ha0 : f a = zero
      · by_cases hb0 : f b = zero
        · rw [ha0, hb0] at gate
          have hz0 := same _ _ gate
          apply noCost _ (.inl hz0)
          have cd := zeroCount_insert f zero z rest hzr
          simp [ha0, hb0, hz0] at ca cb cd
          omega
        · rw [ha0] at gate
          have hz' := leftZero _ _ gate
          apply noCost _ (hz'.imp_right Or.inr)
          simp [ha0, hb0] at ca cb
          omega
      · by_cases hb0 : f b = zero
        · rw [hb0] at gate
          have hz' := rightZero _ _ gate
          apply noCost _ (hz'.imp_right Or.inl)
          simp [ha0, hb0] at ca cb
          omega
        · simp [ha0, hb0] at ca cb
          by_cases heq : f a = f b
          · apply noCost _ (.inr (.inr (same _ _ (heq ▸ gate))))
            omega
          · let initial := insert a (insert b rest)
            let avail := projected f zero initial
            have av : avail = insert (f a) (insert (f b) (projected f zero rest)) := by
              simp [initial, avail, projected_insert, ha0, hb0]
            have moved : projected f zero (insert z rest) ⊆ insert (f z) avail := by
              rw [projected_insert, av]
              by_cases hzero : f z = zero <;> simp [hzero, Finset.subset_iff, Finset.mem_insert] <;> tauto
            have htail := build_mono_set current moved
            have hstep : build op' (f target) (k - zeroCount f zero (insert z rest) + 1) avail :=
              .inr ⟨f a, by simp [av], f b, by simp [av], heq, f z, gate, htail⟩
            have acard := live_card (ops := op) (goal := target) (k := k+1) (s := initial)
              (Or.inr ⟨a, ha, b, hb, hab, z, hz, hzout, rest, rfl, tail⟩)
            have two : ({a,b} : Finset α) ⊆ initial.filter (fun w => f w ≠ zero) := by
              simp [initial, Finset.insert_subset_iff, ha0, hb0]
            have tc := Finset.card_le_card two
            have total := Finset.card_filter_add_card_filter_not (s := initial) (fun w => f w = zero)
            have cbound : zeroCount f zero initial ≤ k := by
              simp [hab] at tc
              unfold zeroCount
              omega
            exact build_mono_budget hstep (by
              change k - zeroCount f zero (insert z rest) + 1 ≤ k + 1 - zeroCount f zero initial
              have hpre := show zeroCount f zero initial ≤ zeroCount f zero (insert z rest) from by
                dsimp [initial]
                omega
              omega)

end Projection

namespace Small

abbrev W := BitVec 64

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 32 := ((x >>> 32) &&& ~~~x).setWidth 32

def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [(0x20218c3101080430 : BitVec 64),
   (0x310108020d53049 : BitVec 64),
   (0x8442210c9222c084 : BitVec 64),
   (0x588c42424c000b02 : BitVec 64),
   (0x887225800011048 : BitVec 64),
   (0x53185082110884b0 : BitVec 64),
   (0xa440050528900101 : BitVec 64),
   (0x208820c6666a06 : BitVec 64)]

def inputs : List W := rawInputs

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

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (32 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (32 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 32, differs i goal := by
  unfold differs
  decide

set_option maxRecDepth 10000 in
theorem cuts_spec (ws : List W) (i : Fin 32) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 64 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
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

abbrev Key := Nat × List W

def insertWord (w : W) : List W → List W
  | [] => [w]
  | v :: vs => if w.toNat ≤ v.toNat then w :: v :: vs else v :: insertWord w vs

lemma mem_insertWord (u w : W) (ws : List W) :
    u ∈ insertWord w ws ↔ u = w ∨ u ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons v vs ih =>
    by_cases h : w.toNat ≤ v.toNat
    · simp [insertWord, h]
    · simp [insertWord, h, ih, or_left_comm]

def canon : List W → List W
  | [] => []
  | w :: ws => insertWord w (canon ws)

lemma mem_canon (u : W) (ws : List W) : u ∈ canon ws ↔ u ∈ ws := by
  induction ws with
  | nil => simp [canon]
  | cons w ws ih => simp [canon, mem_insertWord, ih]

def key (n : Nat) (ws : List W) : Key := (n, canon ws)

lemma key_invariant {n m : Nat} {ws vs : List W} (h : key n ws = key m vs) :
    n = m ∧ ws.toFinset = vs.toFinset := by
  have he : canon ws = canon vs := congrArg Prod.snd h
  refine ⟨congrArg Prod.fst h, ?_⟩
  ext w
  simp only [List.mem_toFinset]
  rw [← mem_canon _ ws, ← mem_canon _ vs, he]

def gateChildren (n : Nat) (a b : W) (r : List W) : List (List W) :=
  let restCuts := cuts r
  (ops a b).flatMap fun w =>
    let newCuts := sep w ||| restCuts
    let keepNone := if r.length ≤ n && newCuts == -1 then [w :: r] else []
    let keepA := if r.length < n && (newCuts ||| sep a == -1) then [w :: a :: r] else []
    let keepB := if r.length < n && (newCuts ||| sep b == -1) then [w :: b :: r] else []
    let keepBoth := if r.length + 2 ≤ n && (newCuts ||| sep a ||| sep b == -1)
      then [w :: a :: b :: r] else []
    keepNone ++ keepA ++ keepB ++ keepBoth

def children (n : Nat) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a, b, r) => gateChildren n a b r

lemma gateChildren_complete {n : Nat} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hlen : kept.length ≤ n) (hc : cuts (z :: kept) = -1) :
    z :: kept ∈ gateChildren n a b r := by
  apply List.mem_flatMap.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · have eq : sep z ||| cuts kept = -1 := hc
    simp [eq, hlen]
  · have eq : sep z ||| cuts r ||| sep a = -1 := by
      rw [← hc]
      simp only [cuts, List.foldr_cons]
      ac_rfl
    have hn : r.length < n := by simp only [List.length_cons] at hlen; omega
    simp [gateChildren, eq, hn]
  · have eq : sep z ||| cuts r ||| sep b = -1 := by
      rw [← hc]
      simp only [cuts, List.foldr_cons]
      ac_rfl
    have hn : r.length < n := by simp only [List.length_cons] at hlen; omega
    simp [gateChildren, eq, hn]
  · have eq : sep z ||| cuts r ||| sep a ||| sep b = -1 := by
      rw [← hc]
      simp only [cuts, List.foldr_cons]
      ac_rfl
    have hn : r.length + 2 ≤ n := by simp only [List.length_cons] at hlen; omega
    simp [gateChildren, eq, hn]

lemma children_complete {n : Nat} {ws : List W} (hn : ws.Nodup)
    (h : live basicOps goal (n + 1) ws.toFinset) :
    ws = [goal] ∨ ∃ l ∈ children n ws, l.Nodup ∧ live basicOps goal n l.toFinset := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (singleton_list hn done)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hm : (a, b, r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        ∃ l ∈ children n ws, l.Nodup ∧ live basicOps goal n l.toFinset := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hlmem := gateChildren_complete (n := n) hop hk (by omega) (cuts_full hl)
      exact ⟨z :: kept, List.mem_flatMap.mpr ⟨(a, b, r), hm, hlmem⟩, hnd, hl⟩
    right
    rcases hm with direct | swap
    · exact go direct hp hs hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

abbrev Cert := Array (List (List W))

def slot (ws : List W) : Nat :=
  ws.foldl (fun h w => (h * 257 + w.toNat) % 127) 0

def lookup (t : Cert) (ws : List W) : Bool :=
  ((t[slot ws]?).getD []).contains ws

def verified (t : Cert) (test : List W → Bool) : Bool :=
  t.toList.all (fun b => b.all test)

lemma found_verified {t : Cert} {test : List W → Bool} {ws : List W}
    (h : verified t test = true) (got : lookup t ws = true) : test ws = true := by
  have allBuckets := List.all_eq_true.mp h
  unfold lookup at got
  by_cases i : slot ws < t.size
  · rw [Array.getElem?_eq_getElem i, Option.getD_some] at got
    exact List.all_eq_true.mp
      (allBuckets _ (Array.mem_toList_iff.mpr (Array.getElem_mem i)))
      _ (List.contains_iff_mem.mp got)
  · simp [Array.getElem?_eq_none (Nat.le_of_not_gt i)] at got

lemma insertWord_perm (w : W) (vs : List W) : (insertWord w vs).Perm (w :: vs) := by
  induction vs with
  | nil => exact .refl _
  | cons v vs ih =>
    by_cases h : w.toNat ≤ v.toNat
    · simp [insertWord, h]
    · exact (by simpa [insertWord, h] using (List.Perm.cons v ih).trans (.swap w v vs))

lemma canon_perm (ws : List W) : (canon ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons w ws ih => exact (insertWord_perm w (canon ws)).trans (.cons w ih)

lemma canon_finset (ws : List W) : (canon ws).toFinset = ws.toFinset := by
  ext w
  simpa using (mem_canon w ws)

def CertSound (n : Nat) (t : Cert) : Prop :=
  ∀ ws, ws.Nodup → lookup t (canon ws) = true → ¬ live basicOps goal n ws.toFinset

def testZero (ws : List W) : Bool :=
  !(ws == [goal])

def testStep (n : Nat) (prev : Cert) (ws : List W) : Bool :=
  if ws == [goal] then false else
    (children n ws).all fun child => if child.Nodup then lookup prev (canon child) else true

lemma certifyZero (t : Cert) (h : verified t testZero = true) : CertSound 0 t := by
  intro ws hnd got hLive
  have bad := found_verified h got
  change ws.toFinset = {goal} at hLive
  have nc := singleton_list ((canon_perm ws).nodup_iff.mpr hnd) (by simpa [canon_finset] using hLive)
  simp [testZero, nc] at bad

lemma certifyStep {n : Nat} {prev t : Cert} (sound : CertSound n prev)
    (h : verified t (testStep n prev) = true) : CertSound (n+1) t := by
  intro ws hnd got hLive
  have allChildren := found_verified h got
  have hcanon : live basicOps goal (n+1) (canon ws).toFinset := by simpa [canon_finset] using hLive
  have ndcanon := (canon_perm ws).nodup_iff.mpr hnd
  obtain done | ⟨child, hchild, ndchild, alive⟩ := children_complete ndcanon hcanon
  · simp [testStep, done] at allChildren
  · have handle : (if child.Nodup then lookup prev (canon child) else true) = true := by
      unfold testStep at allChildren
      split at allChildren
      · contradiction
      · exact List.all_eq_true.mp allChildren child hchild
    exact (sound child ndchild (by simpa [ndchild] using handle)) alive

def noRows : Cert := #[]

theorem inputs_nodup : inputs.Nodup := by decide +kernel
theorem inputs_length : inputs.length = 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem front_small : (inputs.sublists.filter (fun l => decide (l.length < 8))).all
    (fun l => cuts l != -1) = true := by decide +kernel

theorem all_inputs {k : Nat} {s : Finset W} (subset : s ⊆ inputs.toFinset)
    (h : live basicOps goal k s) : s = inputs.toFinset := by
  let l := inputs.filter (fun w => decide (w ∈ s))
  have hlS : l.toFinset = s := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (subset h), h⟩⟩
  have hsl : l.Sublist inputs := List.filter_sublist
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr hsl
  by_cases hlen : l.length < 8
  · have hrow := List.all_eq_true.mp front_small l
      (List.mem_filter.mpr ⟨hmem, by simpa using hlen⟩)
    have hc : cuts l = -1 := cuts_full (hlS ▸ h)
    simp [hc] at hrow
  · have hle := hsl.length_le
    rw [inputs_length] at hle
    have hl := hsl.eq_of_length (by rw [inputs_length]; omega : l.length = inputs.length)
    rw [← hlS, hl]

def word0 : W := (0x20882000000000 : BitVec 64)
def word1 : W := (0x208820c6666a06 : BitVec 64)
def word2 : W := (0x310108000000000 : BitVec 64)
def word3 : W := (0x310108020d53049 : BitVec 64)
def word4 : W := (0x33098a000000000 : BitVec 64)
def word5 : W := (0x33098a020d53049 : BitVec 64)
def word6 : W := (0x33098a0c6666a06 : BitVec 64)
def word7 : W := (0x33098a0e6f77a4f : BitVec 64)
def word8 : W := (0x887225800011048 : BitVec 64)
def word9 : W := (0x8a7aa7800011048 : BitVec 64)
def word10 : W := (0x8a7aa78c6677a4e : BitVec 64)
def word11 : W := (0xb9732d800011048 : BitVec 64)
def word12 : W := (0xb9732d820d53049 : BitVec 64)
def word13 : W := (0xbb7baf800011048 : BitVec 64)
def word14 : W := (0xbb7baf820d53049 : BitVec 64)
def word15 : W := (0xbb7baf8e6f77a4f : BitVec 64)
def word16 : W := (0x20218c3101080430 : BitVec 64)
def word17 : W := (0x5318508200000000 : BitVec 64)
def word18 : W := (0x53185082110884b0 : BitVec 64)
def word19 : W := (0x588c42424c000b02 : BitVec 64)
def word20 : W := (0x58acca624c000b02 : BitVec 64)
def word21 : W := (0x58acca62ce666b06 : BitVec 64)
def word22 : W := (0x5b9c52c24c000b02 : BitVec 64)
def word23 : W := (0x5b9c52c26cd53b4b : BitVec 64)
def word24 : W := (0x5bbcdae24c000b02 : BitVec 64)
def word25 : W := (0x5bbcdae2ce666b06 : BitVec 64)
def word26 : W := (0x5bbcdae2eef77b4f : BitVec 64)
def word27 : W := (0x7339dcb3110884b0 : BitVec 64)
def word28 : W := (0x8442210c9222c084 : BitVec 64)
def word29 : W := (0x8462a92c9222c084 : BitVec 64)
def word30 : W := (0x8462a92cd666ea86 : BitVec 64)
def word31 : W := (0xa440050528900101 : BitVec 64)
def word32 : W := (0xa4608d2528900101 : BitVec 64)
def word33 : W := (0xa4608d25eef66b07 : BitVec 64)
def word34 : W := (0xa463ad3d932ac4b4 : BitVec 64)
def word35 : W := (0xa750158528900101 : BitVec 64)
def word36 : W := (0xa750158528d53149 : BitVec 64)
def word37 : W := (0xa7709da528900101 : BitVec 64)
def word38 : W := (0xa7709da528d53149 : BitVec 64)
def word39 : W := (0xa7709da5eef77b4f : BitVec 64)
def word40 : W := (0xacc7275d28911149 : BitVec 64)
def word41 : W := (0xafd737dd28d53149 : BitVec 64)
def word42 : W := (0xd75a718e932ac4b4 : BitVec 64)
def word43 : W := (0xf77bfdbf932ac4b4 : BitVec 64)
def word44 : W := (0xfccc47476c900b03 : BitVec 64)
def word45 : W := (0xfceccf676c900b03 : BitVec 64)
def word46 : W := (0xfceccf67eef66b07 : BitVec 64)
def word47 : W := (0xffdc57c76c900b03 : BitVec 64)
def word48 : W := (0xffdc57c76cd53b4b : BitVec 64)
def word49 : W := (0xfffcdfe76c900b03 : BitVec 64)
def word50 : W := (0xfffcdfe7eef77b4f : BitVec 64)

def layer0 : Cert := noRows

def layer1 : Cert := noRows

def layer2 : Cert := #[
  [],
  [],
  [],
  [],
  [],
  [],
  [[word13, word43, word44]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word8, word43, word49]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []]

def layer3 : Cert := #[
  [],
  [],
  [[word8, word19, word37, word43]],
  [],
  [[word8, word24, word31, word43]],
  [],
  [],
  [[word8, word20, word36, word43]],
  [],
  [],
  [[word13, word19, word31, word43]],
  [],
  [[word4, word8, word43, word44]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word13, word27, word28, word44]],
  [],
  [],
  [],
  [[word12, word19, word32, word43]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word8, word19, word38, word43]],
  [],
  [],
  [[word3, word8, word43, word45]],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word5, word8, word43, word44]],
  [],
  [],
  [[word14, word19, word31, word43]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word9, word19, word36, word43]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word3, word9, word43, word44]],
  [],
  [],
  [[word12, word20, word31, word43]],
  [],
  [[word8, word27, word28, word49]],
  [],
  [],
  []]

def layer4 : Cert := #[
  [],
  [],
  [[word3, word9, word27, word28, word44], [word8, word16, word21, word42, word48], [word8, word25, word27, word28, word31]],
  [],
  [],
  [[word6, word8, word27, word28, word44]],
  [],
  [[word15, word19, word27, word28, word40]],
  [],
  [[word3, word8, word20, word31, word43]],
  [],
  [],
  [],
  [[word8, word19, word27, word28, word37]],
  [],
  [],
  [[word8, word21, word27, word36, word43], [word14, word16, word19, word31, word42]],
  [[word12, word18, word20, word31, word34]],
  [[word1, word11, word16, word42, word44], [word10, word12, word16, word42, word44]],
  [],
  [],
  [[word8, word21, word27, word28, word36]],
  [],
  [[word8, word18, word19, word34, word38]],
  [],
  [[word9, word18, word19, word34, word36], [word11, word21, word27, word28, word31]],
  [[word7, word8, word27, word28, word44]],
  [[word12, word19, word27, word28, word32]],
  [[word4, word8, word19, word31, word43]],
  [[word14, word19, word27, word28, word31]],
  [],
  [[word3, word8, word16, word42, word45], [word3, word8, word18, word34, word45]],
  [],
  [[word5, word8, word16, word42, word44], [word5, word8, word18, word34, word44]],
  [[word12, word20, word27, word28, word31]],
  [],
  [],
  [],
  [[word3, word9, word16, word42, word44], [word3, word9, word18, word34, word44]],
  [],
  [[word7, word8, word27, word43, word44]],
  [[word7, word8, word27, word42, word44]],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word8, word16, word20, word36, word42], [word12, word21, word27, word28, word40]],
  [],
  [],
  [],
  [],
  [],
  [[word8, word21, word27, word34, word36], [word12, word21, word27, word28, word44]],
  [],
  [],
  [],
  [],
  [[word7, word8, word27, word34, word44]],
  [],
  [],
  [],
  [],
  [[word8, word24, word27, word28, word31]],
  [[word1, word8, word27, word28, word47], [word4, word8, word27, word28, word44], [word12, word16, word20, word31, word42]],
  [[word3, word8, word19, word32, word43], [word8, word27, word28, word44, word50]],
  [],
  [],
  [[word0, word3, word8, word43, word44]],
  [],
  [],
  [[word0, word12, word19, word31, word43]],
  [],
  [[word8, word18, word20, word34, word36], [word12, word18, word19, word32, word34]],
  [],
  [[word8, word19, word27, word28, word38]],
  [],
  [[word9, word19, word27, word28, word36]],
  [],
  [[word12, word16, word21, word42, word44]],
  [],
  [[word13, word19, word27, word28, word31]],
  [[word8, word20, word27, word28, word36]],
  [],
  [[word0, word8, word19, word36, word43], [word8, word21, word27, word28, word35]],
  [],
  [[word5, word8, word19, word31, word43]],
  [],
  [],
  [[word8, word27, word28, word36, word46]],
  [[word8, word26, word27, word28, word44]],
  [[word3, word9, word19, word31, word43]],
  [],
  [],
  [[word14, word18, word19, word31, word34]],
  [[word8, word16, word42, word46, word48]],
  [[word10, word16, word19, word41, word42]],
  [],
  [[word8, word15, word27, word28, word44]],
  [],
  [[word1, word8, word16, word42, word47], [word8, word21, word27, word36, word42]],
  [],
  [[word8, word21, word27, word28, word48]],
  [[word15, word16, word19, word41, word42]],
  [[word8, word16, word19, word38, word42]],
  [],
  [],
  [],
  [[word1, word11, word27, word28, word44], [word10, word12, word27, word28, word44]],
  [],
  [],
  [[word8, word27, word28, word39, word44]],
  [[word10, word19, word27, word28, word41]],
  [],
  [[word8, word27, word28, word46, word48]],
  [[word8, word21, word27, word28, word41]],
  [],
  [],
  [],
  [[word15, word19, word27, word28, word41]],
  [],
  [[word3, word8, word27, word28, word45], [word12, word16, word19, word32, word42]],
  [],
  [[word5, word8, word27, word28, word44]],
  [],
  [[word9, word16, word19, word36, word42]]]

def layer5 : Cert := #[
  [],
  [[word0, word12, word16, word19, word31, word42], [word1, word11, word16, word19, word31, word42], [word5, word8, word16, word18, word28, word44], [word8, word16, word19, word30, word36, word42], [word10, word12, word16, word19, word31, word42]],
  [],
  [[word3, word8, word16, word30, word42, word44]],
  [[word8, word19, word27, word28, word33, word36]],
  [[word1, word8, word19, word27, word36, word43], [word8, word16, word17, word19, word30, word31]],
  [[word8, word16, word18, word21, word34, word36]],
  [[word1, word12, word16, word19, word41, word42], [word12, word16, word18, word19, word29, word31]],
  [[word1, word8, word23, word27, word28, word44]],
  [[word1, word8, word21, word27, word28, word36], [word4, word8, word19, word27, word28, word31]],
  [[word0, word8, word18, word19, word34, word36], [word1, word8, word12, word16, word42, word44], [word1, word8, word19, word27, word28, word36], [word12, word16, word19, word31, word33, word42]],
  [[word3, word8, word10, word16, word42, word44]],
  [],
  [[word3, word9, word18, word19, word31, word34], [word8, word16, word21, word23, word31, word42], [word14, word16, word18, word19, word28, word31]],
  [[word0, word12, word19, word27, word28, word31], [word1, word7, word8, word27, word28, word44], [word1, word11, word19, word27, word28, word31], [word3, word8, word16, word18, word28, word45], [word10, word12, word19, word27, word28, word31], [word10, word16, word18, word19, word28, word41]],
  [[word8, word16, word18, word30, word36, word44]],
  [[word1, word8, word16, word18, word28, word47], [word3, word9, word16, word18, word28, word44], [word8, word16, word21, word27, word28, word36]],
  [[word3, word8, word21, word27, word28, word31], [word3, word8, word27, word28, word44, word46]],
  [[word0, word3, word8, word16, word42, word44], [word0, word3, word8, word18, word34, word44], [word7, word8, word21, word27, word28, word31]],
  [[word7, word8, word19, word27, word28, word31]],
  [],
  [[word8, word21, word27, word28, word36]],
  [[word1, word12, word19, word27, word31, word43]],
  [[word1, word12, word19, word27, word28, word41]],
  [],
  [[word3, word7, word8, word16, word42, word44], [word3, word8, word27, word28, word31, word46], [word6, word8, word16, word18, word28, word44], [word8, word12, word21, word27, word28, word31], [word8, word16, word19, word33, word36, word42]],
  [[word1, word12, word16, word19, word42, word44], [word7, word8, word27, word28, word44], [word12, word16, word18, word19, word28, word32]],
  [[word3, word8, word16, word33, word42, word44]],
  [],
  [],
  [],
  [[word1, word8, word27, word28, word36, word44], [word7, word8, word18, word27, word28, word44], [word8, word16, word18, word25, word28, word31]],
  [],
  [[word1, word2, word8, word16, word42, word44]],
  [[word7, word8, word16, word19, word36, word42]],
  [[word15, word16, word18, word19, word28, word41]],
  [[word3, word8, word21, word27, word31, word42], [word8, word16, word18, word20, word28, word36]],
  [[word1, word12, word19, word27, word28, word40], [word8, word16, word18, word21, word28, word35]],
  [[word7, word8, word19, word27, word31, word42]],
  [[word3, word8, word27, word28, word33, word44]],
  [[word3, word8, word16, word19, word32, word42]],
  [],
  [[word3, word8, word21, word27, word31, word34]],
  [[word1, word8, word19, word27, word34, word36], [word1, word12, word19, word27, word28, word44]],
  [[word7, word8, word19, word27, word31, word34]],
  [],
  [[word5, word8, word16, word19, word31, word42], [word11, word16, word18, word21, word28, word31]],
  [],
  [],
  [[word1, word12, word16, word19, word40, word42], [word8, word21, word26, word27, word28, word31], [word15, word16, word18, word19, word28, word40]],
  [],
  [[word7, word12, word16, word19, word31, word42]],
  [[word8, word19, word26, word27, word28, word31]],
  [[word8, word15, word16, word18, word28, word44], [word8, word16, word18, word21, word36, word42]],
  [],
  [[word1, word8, word16, word22, word31, word42], [word1, word12, word19, word27, word28, word36], [word8, word16, word18, word21, word28, word48]],
  [[word1, word3, word8, word27, word28, word44]],
  [],
  [[word1, word8, word16, word19, word36, word42]],
  [[word5, word8, word19, word27, word28, word31]],
  [],
  [[word3, word9, word16, word19, word31, word42]],
  [[word3, word8, word18, word20, word31, word34]],
  [[word0, word8, word19, word27, word28, word36], [word8, word16, word18, word22, word30, word31]],
  [[word7, word12, word19, word27, word28, word31], [word8, word19, word21, word27, word28, word36]],
  [],
  [],
  [[word8, word21, word27, word28, word31, word36]],
  [[word8, word16, word18, word21, word28, word41]],
  [[word1, word8, word16, word23, word42, word44], [word8, word16, word18, word19, word30, word35]],
  [[word1, word3, word8, word27, word43, word44], [word1, word8, word16, word42, word44, word48], [word8, word16, word18, word28, word44, word50]],
  [[word1, word3, word8, word27, word42, word44], [word8, word10, word19, word27, word28, word36]],
  [[word0, word3, word8, word19, word31, word43], [word3, word8, word19, word27, word28, word32]],
  [[word8, word16, word18, word26, word28, word44]],
  [[word1, word8, word19, word27, word28, word35], [word3, word9, word19, word27, word28, word31]],
  [[word1, word8, word16, word19, word42, word48], [word1, word12, word16, word19, word31, word42]],
  [],
  [[word12, word16, word18, word20, word28, word31]],
  [[word3, word8, word21, word27, word31, word43], [word11, word16, word18, word19, word30, word31]],
  [[word3, word8, word20, word27, word28, word31]],
  [[word0, word12, word18, word19, word31, word34], [word1, word8, word16, word36, word42, word44], [word7, word8, word19, word27, word31, word43]],
  [],
  [],
  [[word1, word11, word16, word18, word28, word44], [word6, word8, word19, word27, word28, word31], [word10, word12, word16, word18, word28, word44]],
  [],
  [[word7, word8, word16, word27, word28, word44]],
  [],
  [],
  [[word1, word12, word19, word27, word28, word31], [word7, word8, word16, word18, word28, word44]],
  [[word1, word3, word8, word27, word34, word44], [word1, word8, word16, word19, word41, word42], [word1, word8, word27, word28, word44, word48], [word12, word19, word27, word28, word31, word33]],
  [[word1, word8, word19, word27, word36, word42], [word3, word10, word19, word27, word28, word40], [word12, word16, word18, word21, word28, word40]],
  [[word1, word3, word8, word16, word43, word44], [word3, word8, word21, word27, word30, word31]],
  [[word1, word3, word8, word16, word42, word44], [word1, word8, word19, word27, word28, word48]],
  [[word3, word8, word21, word27, word28, word40], [word7, word8, word19, word27, word30, word31], [word8, word16, word18, word19, word29, word36], [word8, word19, word27, word28, word31, word39]],
  [[word2, word8, word21, word27, word28, word31], [word8, word16, word18, word28, word36, word46]],
  [[word7, word8, word19, word27, word28, word40]],
  [[word12, word16, word18, word21, word28, word44]],
  [],
  [],
  [[word3, word8, word21, word27, word28, word44], [word9, word16, word18, word19, word28, word36]],
  [[word1, word8, word16, word19, word36, word43], [word8, word16, word17, word21, word28, word31], [word8, word16, word18, word21, word28, word36]],
  [[word1, word8, word12, word27, word28, word44], [word1, word8, word16, word17, word28, word44], [word7, word8, word19, word27, word28, word44]],
  [[word3, word8, word10, word27, word28, word44], [word3, word10, word16, word19, word40, word42]],
  [[word1, word12, word16, word19, word36, word42], [word7, word8, word16, word18, word42, word44], [word12, word16, word19, word21, word31, word42]],
  [],
  [[word1, word8, word19, word27, word28, word41], [word8, word21, word23, word27, word28, word31], [word12, word19, word21, word27, word28, word31]],
  [[word7, word8, word27, word28, word31, word44], [word12, word15, word16, word19, word31, word42]],
  [[word1, word12, word19, word27, word31, word42]],
  [[word8, word18, word21, word27, word28, word36], [word12, word16, word19, word30, word31, word42]],
  [[word0, word3, word8, word27, word28, word44]],
  [[word3, word8, word16, word20, word31, word42]],
  [[word0, word8, word16, word19, word36, word42], [word3, word8, word21, word27, word28, word36], [word8, word15, word19, word27, word28, word31]],
  [[word8, word16, word18, word19, word28, word38]],
  [[word1, word12, word19, word27, word31, word34], [word7, word8, word19, word27, word28, word36]],
  [],
  [],
  [[word3, word7, word8, word27, word28, word44], [word8, word16, word18, word28, word39, word44]],
  [[word1, word12, word16, word19, word31, word43]],
  [[word1, word8, word22, word27, word28, word31]],
  [[word3, word8, word18, word19, word32, word34], [word8, word10, word16, word19, word36, word42], [word8, word16, word18, word28, word46, word48], [word12, word15, word19, word27, word28, word31]],
  [],
  [[word7, word8, word16, word18, word34, word44], [word8, word19, word27, word28, word36, word39]],
  [[word3, word8, word16, word18, word29, word44], [word8, word16, word19, word36, word39, word42], [word12, word16, word18, word19, word30, word40]],
  [[word1, word8, word16, word19, word35, word42], [word8, word16, word19, word21, word36, word42]],
  [[word1, word2, word8, word27, word28, word44]],
  [[word3, word8, word16, word21, word42, word44], [word3, word8, word16, word42, word44, word46], [word5, word8, word18, word19, word31, word34]],
  []]

def layer6 : Cert := #[
  [],
  [[word0, word3, word8, word16, word19, word31, word42], [word1, word2, word8, word16, word18, word28, word44], [word1, word3, word8, word19, word27, word31, word42]],
  [[word7, word8, word16, word18, word19, word31, word42]],
  [[word3, word8, word16, word18, word19, word30, word40], [word3, word8, word16, word18, word30, word31, word44]],
  [],
  [[word8, word15, word16, word18, word19, word28, word31]],
  [],
  [[word1, word3, word8, word19, word27, word31, word34]],
  [[word7, word8, word16, word18, word19, word31, word34]],
  [],
  [[word1, word8, word19, word27, word28, word36], [word8, word16, word18, word21, word26, word28, word31]],
  [[word1, word3, word8, word16, word19, word31, word43], [word1, word8, word16, word18, word28, word36, word44], [word8, word16, word18, word19, word26, word28, word31]],
  [[word1, word12, word16, word18, word19, word28, word40]],
  [[word3, word8, word16, word19, word27, word30, word31]],
  [[word0, word3, word8, word19, word27, word28, word31], [word1, word3, word12, word16, word19, word31, word42]],
  [[word3, word8, word16, word18, word19, word29, word31]],
  [],
  [[word3, word8, word21, word27, word28, word31]],
  [[word1, word12, word16, word18, word19, word28, word44], [word3, word8, word16, word19, word31, word33, word42]],
  [[word7, word8, word19, word27, word28, word31], [word8, word16, word18, word19, word23, word30, word31], [word8, word16, word18, word19, word30, word31, word36]],
  [],
  [[word3, word9, word16, word18, word19, word28, word31]],
  [[word1, word8, word16, word17, word19, word28, word31], [word1, word8, word16, word18, word19, word28, word36], [word1, word12, word16, word19, word27, word28, word31], [word3, word7, word8, word16, word19, word31, word42], [word3, word8, word16, word18, word21, word28, word31]],
  [],
  [],
  [[word7, word8, word16, word18, word21, word28, word31]],
  [],
  [[word1, word3, word12, word19, word27, word28, word31]],
  [],
  [[word12, word15, word16, word18, word19, word28, word31]],
  [[word1, word12, word16, word18, word19, word28, word36], [word3, word8, word18, word21, word27, word28, word31]],
  [[word2, word8, word16, word18, word19, word30, word31]],
  [],
  [],
  [[word1, word8, word19, word27, word28, word31, word36], [word3, word8, word16, word18, word19, word28, word32], [word7, word8, word18, word19, word27, word28, word31], [word12, word16, word18, word19, word28, word30, word31]],
  [[word3, word7, word8, word19, word27, word28, word31]],
  [],
  [],
  [[word7, word8, word16, word18, word28, word31, word44]],
  [],
  [],
  [[word3, word8, word16, word18, word21, word31, word42]],
  [],
  [[word1, word3, word8, word19, word27, word31, word43]],
  [[word3, word10, word16, word18, word19, word28, word40]],
  [],
  [[word1, word2, word8, word16, word19, word31, word42], [word8, word12, word16, word18, word21, word28, word31]],
  [[word1, word3, word8, word16, word19, word42, word44], [word3, word8, word16, word18, word21, word31, word34]],
  [[word1, word3, word8, word16, word27, word28, word44], [word6, word8, word16, word18, word19, word28, word31]],
  [],
  [[word8, word16, word18, word21, word28, word31, word36], [word12, word16, word18, word19, word21, word28, word31]],
  [[word1, word3, word8, word16, word18, word28, word44]],
  [[word1, word7, word8, word16, word18, word28, word44]],
  [],
  [[word0, word8, word16, word18, word19, word28, word36], [word3, word8, word16, word18, word19, word30, word31]],
  [[word1, word8, word16, word18, word19, word34, word36]],
  [[word1, word3, word8, word19, word27, word30, word31], [word1, word3, word8, word27, word28, word44]],
  [[word7, word8, word16, word18, word19, word30, word31]],
  [[word1, word3, word8, word19, word27, word28, word40], [word1, word8, word16, word19, word36, word42]],
  [[word1, word2, word8, word19, word27, word28, word31], [word1, word8, word12, word16, word18, word28, word44], [word7, word8, word16, word18, word19, word28, word40]],
  [[word1, word8, word16, word19, word31, word36, word42]],
  [],
  [[word1, word3, word8, word16, word31, word42, word44], [word3, word8, word10, word16, word18, word28, word44]],
  [[word1, word12, word16, word18, word19, word28, word31]],
  [[word1, word3, word8, word19, word27, word28, word44], [word1, word8, word16, word18, word21, word28, word36]],
  [[word3, word8, word16, word21, word27, word28, word31], [word7, word8, word16, word18, word19, word28, word44]],
  [[word1, word3, word8, word16, word18, word42, word44]],
  [],
  [],
  [[word1, word3, word8, word27, word28, word31, word44], [word1, word8, word16, word18, word28, word44, word48], [word7, word8, word16, word19, word27, word28, word31]],
  [[word1, word3, word8, word16, word19, word40, word42]],
  [[word8, word16, word18, word21, word23, word28, word31]],
  [[word1, word8, word19, word23, word27, word28, word31]],
  [[word1, word8, word18, word19, word27, word28, word36]],
  [[word3, word8, word16, word18, word28, word44, word46], [word8, word16, word18, word19, word28, word31, word39]],
  [[word1, word12, word16, word19, word31, word42]],
  [[word1, word3, word8, word19, word27, word28, word36]],
  [[word7, word8, word16, word18, word19, word28, word36]],
  [[word8, word10, word16, word18, word19, word28, word36], [word8, word12, word16, word18, word19, word30, word31]],
  [],
  [[word0, word3, word8, word18, word19, word31, word34], [word1, word8, word16, word18, word22, word28, word31]],
  [],
  [[word1, word12, word16, word18, word19, word31, word42], [word3, word8, word16, word18, word28, word31, word46]],
  [[word0, word3, word8, word16, word18, word28, word44]],
  [[word1, word3, word8, word16, word18, word34, word44]],
  [[word3, word8, word16, word18, word20, word28, word31]],
  [[word1, word8, word16, word18, word19, word28, word35], [word12, word16, word18, word19, word28, word31, word33]],
  [],
  [[word1, word12, word16, word18, word19, word31, word34], [word1, word12, word19, word27, word28, word31], [word3, word8, word16, word18, word28, word30, word44], [word7, word8, word16, word18, word28, word44]],
  [],
  [],
  [],
  [[word1, word3, word8, word16, word42, word44]],
  [],
  [],
  [[word0, word12, word16, word18, word19, word28, word31], [word1, word11, word16, word18, word19, word28, word31], [word10, word12, word16, word18, word19, word28, word31]],
  [[word1, word3, word8, word16, word19, word31, word42], [word3, word8, word16, word18, word21, word30, word31], [word3, word8, word16, word18, word28, word33, word44]],
  [[word3, word8, word19, word27, word28, word31, word33]],
  [[word1, word8, word16, word18, word23, word28, word44], [word3, word8, word16, word18, word21, word28, word40]],
  [],
  [[word8, word16, word18, word21, word28, word36]],
  [],
  [[word1, word8, word16, word18, word19, word36, word42], [word8, word16, word18, word19, word28, word36, word39]],
  [[word5, word8, word16, word18, word19, word28, word31]],
  [[word1, word8, word12, word16, word19, word31, word42], [word1, word8, word16, word18, word19, word28, word48], [word1, word12, word16, word19, word28, word31, word42], [word3, word7, word8, word16, word18, word28, word44], [word3, word8, word16, word18, word21, word28, word44], [word8, word16, word18, word19, word28, word30, word36]],
  [[word1, word8, word16, word19, word23, word31, word42]],
  [],
  [[word3, word8, word10, word16, word19, word31, word42]],
  [[word1, word3, word8, word21, word27, word28, word31], [word1, word8, word16, word19, word27, word28, word36]],
  [[word1, word3, word8, word19, word27, word28, word31]],
  [[word1, word7, word8, word19, word27, word28, word31], [word7, word8, word16, word18, word19, word28, word31]],
  [[word3, word8, word16, word19, word21, word31, word42]],
  [[word8, word16, word18, word19, word28, word33, word36]],
  [[word3, word8, word19, word21, word27, word28, word31]],
  [[word1, word12, word18, word19, word27, word28, word31]],
  [],
  [[word3, word8, word16, word18, word21, word28, word36], [word3, word8, word16, word19, word30, word31, word42]],
  [[word1, word8, word12, word19, word27, word28, word31], [word1, word8, word16, word18, word19, word28, word41]],
  [[word7, word12, word16, word18, word19, word28, word31]],
  [],
  [[word3, word8, word10, word19, word27, word28, word31], [word8, word16, word18, word19, word21, word28, word36]],
  [[word1, word3, word8, word18, word27, word28, word44]],
  [],
  [],
  [[word1, word3, word8, word16, word19, word36, word42], [word1, word8, word16, word19, word28, word36, word42]],
  [[word1, word12, word16, word18, word19, word28, word41]],
  [[word1, word3, word8, word16, word28, word42, word44], [word2, word8, word16, word18, word21, word28, word31]]]

def layer7 : Cert := #[
  [],
  [],
  [[word1, word7, word8, word16, word18, word19, word28, word31]],
  [],
  [],
  [],
  [],
  [[word1, word3, word12, word16, word18, word19, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word1, word3, word8, word16, word18, word19, word31, word42]],
  [],
  [],
  [],
  [[word1, word8, word16, word18, word19, word28, word36], [word3, word8, word16, word18, word21, word28, word31]],
  [[word1, word8, word12, word16, word18, word19, word28, word31]],
  [[word1, word3, word8, word16, word18, word19, word31, word34]],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word3, word7, word8, word16, word18, word19, word28, word31]],
  [[word3, word8, word10, word16, word18, word19, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word1, word3, word8, word16, word19, word28, word31, word42]],
  [[word1, word3, word8, word16, word18, word21, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word1, word3, word8, word18, word19, word27, word28, word31]],
  [[word1, word3, word8, word16, word18, word28, word44]],
  [],
  [],
  [[word1, word3, word8, word16, word18, word28, word31, word44], [word3, word8, word16, word18, word19, word30, word31]],
  [],
  [],
  [],
  [[word3, word8, word16, word18, word19, word28, word30, word31]],
  [],
  [],
  [],
  [],
  [[word1, word12, word16, word18, word19, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word1, word8, word16, word18, word19, word28, word31, word36]],
  [],
  [],
  [[word1, word3, word8, word16, word18, word19, word30, word31]],
  [[word3, word8, word16, word18, word19, word21, word28, word31]],
  [[word1, word3, word8, word16, word18, word19, word28, word40]],
  [],
  [],
  [],
  [],
  [],
  [[word1, word3, word8, word16, word18, word19, word28, word44]],
  [],
  [],
  [],
  [[word1, word3, word8, word16, word19, word27, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [[word1, word8, word16, word18, word19, word23, word28, word31]],
  [],
  [[word1, word3, word8, word16, word18, word19, word28, word36]],
  [],
  [[word0, word3, word8, word16, word18, word19, word28, word31]],
  [[word1, word3, word8, word16, word19, word31, word42]],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word1, word2, word8, word16, word18, word19, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [[word1, word3, word8, word19, word27, word28, word31]],
  [[word3, word8, word16, word18, word19, word28, word31, word33], [word7, word8, word16, word18, word19, word28, word31]],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []]

def layer8 : Cert := #[
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [[word1, word3, word8, word16, word18, word19, word28, word31]]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck1 : verified layer1 (testStep 0 layer0) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck2 : verified layer2 (testStep 1 layer1) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck3 : verified layer3 (testStep 2 layer2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck4 : verified layer4 (testStep 3 layer3) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck5 : verified layer5 (testStep 4 layer4) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck6 : verified layer6 (testStep 5 layer5) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck7 : verified layer7 (testStep 6 layer6) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma layerCheck8 : verified layer8 (testStep 7 layer7) = true := by decide +kernel

lemma sound0 : CertSound 0 layer0 := certifyZero _ rfl
lemma sound1 : CertSound 1 layer1 := certifyStep sound0 layerCheck1
lemma sound2 : CertSound 2 layer2 := certifyStep sound1 layerCheck2
lemma sound3 : CertSound 3 layer3 := certifyStep sound2 layerCheck3
lemma sound4 : CertSound 4 layer4 := certifyStep sound3 layerCheck4
lemma sound5 : CertSound 5 layer5 := certifyStep sound4 layerCheck5
lemma sound6 : CertSound 6 layer6 := certifyStep sound5 layerCheck6
lemma sound7 : CertSound 7 layer7 := certifyStep sound6 layerCheck7
lemma sound8 : CertSound 8 layer8 := certifyStep sound7 layerCheck8

lemma computed : lookup layer8 (canon inputs) = true := by decide +kernel

theorem no_small (h : build basicOps goal 8 inputs.toFinset) : False := by
  obtain ⟨s, hsub, hl⟩ := compress h
  have hfixed := all_inputs hsub hl
  exact sound8 inputs inputs_nodup computed (hfixed ▸ hl)

end Small

namespace Large

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [((0x1cd8736120218c31 : BitVec 64) ++ (0x23d88f6201080430 : BitVec 64)),
   ((0x2020808203101080 : BitVec 64) ++ (0xd027409d20d53049 : BitVec 64)),
   ((0x400100048442210c : BitVec 64) ++ (0x9222c084 : BitVec 64)),
   ((0x83020c0800000000 : BitVec 64) ++ (0xc00300000000000 : BitVec 64)),
   ((0x40010588c4242 : BitVec 64) ++ (0x4c000b02 : BitVec 64)),
   ((0xdc0f703d00000000 : BitVec 64) ++ (0xd027409d00000000 : BitVec 64)),
   ((0x110044008872258 : BitVec 64) ++ (0x11048 : BitVec 64)),
   ((0x2220888253185082 : BitVec 64) ++ (0x23d88f62110884b0 : BitVec 64)),
   ((0x400100a4400505 : BitVec 64) ++ (0x400100028900101 : BitVec 64)),
   ((0x80020000208820 : BitVec 64) ++ (0x8002000c6666a06 : BitVec 64))]

def inputs : List W := rawInputs

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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

set_option maxRecDepth 10000 in
theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
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
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def A : Fin 5 → Fin 5 → Bool := fun u v => (7580827 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 5 × Fin 5) :=
  [(0, 0), (0, 1), (0, 3), (0, 4), (1, 2), (2, 0), (2, 1), (2, 3), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def negL : List (Fin 5 × Fin 5) :=
  [(0, 2), (1, 0), (1, 1), (1, 3), (1, 4), (2, 2), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4)]

def sampleIndices : List Nat :=
  [25, 153, 83, 68, 11, 33, 134, 49, 86, 142, 22, 43, 46, 70, 149, 38, 13, 72, 136, 143, 47, 39, 81, 135, 44, 50, 87, 141, 148, 25, 153, 83, 1, 44, 56, 89, 122, 0, 11, 45, 22, 33, 99, 110, 7, 8, 1, 44, 56, 89, 122, 0, 11, 45, 22, 33, 99, 110, 7, 8, 1, 44, 56, 89]

def samp (k : Fin 128) : Fin 5 × Fin 5 :=
  let pair := sampleIndices.getD (k.val % 64) 0
  if k.val < 64 then negL.getD (pair % 11) (0, 0)
  else posL.getD (pair / 11) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem inputs_nodup : inputs.Nodup := by decide +kernel

theorem inputs_length : inputs.length = 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem front_small : (inputs.sublists.filter (fun l => decide (l.length < 10))).all
    (fun l => cuts l != -1) = true := by
  decide +kernel

theorem all_inputs {k : Nat} {s : Finset W} (subset : s ⊆ inputs.toFinset)
    (h : live basicOps goal k s) : s = inputs.toFinset := by
  let l := inputs.filter (fun w => decide (w ∈ s))
  have hlS : l.toFinset = s := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (subset h), h⟩⟩
  have hsl : l.Sublist inputs := List.filter_sublist
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr hsl
  by_cases hlen : l.length < 10
  · have hrow := List.all_eq_true.mp front_small l
      (List.mem_filter.mpr ⟨hmem, by simpa using hlen⟩)
    have hc : cuts l = -1 := cuts_full (hlS ▸ h)
    simp [hc] at hrow
  · have hle := hsl.length_le
    rw [inputs_length] at hle
    have hl := hsl.eq_of_length (by rw [inputs_length]; omega : l.length = inputs.length)
    rw [← hlS, hl]


end Large


def toSmall (w : Large.W) : Small.W :=
  ((w >>> 64).setWidth 32) ++ (w.setWidth 32)

lemma toSmall_ops (a b z : Large.W) (hz : z ∈ Large.basicOps a b) :
    toSmall z ∈ Small.basicOps (toSmall a) (toSmall b) := by
  simp [Large.basicOps, Large.ops] at hz
  rcases hz with rfl | rfl
  · have eq : toSmall (a &&& b) = toSmall a &&& toSmall b := by
      simp only [toSmall, BitVec.ushiftRight_and_distrib, BitVec.setWidth_and]
      exact BitVec.and_append.symm
    simp [Small.basicOps, Small.ops, eq]
  · have eq : toSmall (a ||| b) = toSmall a ||| toSmall b := by
      simp only [toSmall, BitVec.ushiftRight_or_distrib, BitVec.setWidth_or]
      exact BitVec.or_append.symm
    simp [Small.basicOps, Small.ops, eq]

lemma left_zero (b z : Small.W) (h : z ∈ Small.basicOps 0 b) : z = 0 ∨ z = b := by
  simpa [Small.basicOps, Small.ops] using h

lemma right_zero (a z : Small.W) (h : z ∈ Small.basicOps a 0) : z = 0 ∨ z = a := by
  simpa [Small.basicOps, Small.ops, or_comm] using h

lemma same_word (a z : Small.W) (h : z ∈ Small.basicOps a a) : z = a := by
  simpa [Small.basicOps, Small.ops] using h

lemma projection_goal : toSmall Large.goal = Small.goal := by decide +kernel
lemma projection_nonzero : toSmall Large.goal ≠ 0 := by decide +kernel
lemma projection_saves : zeroCount toSmall 0 Large.inputs.toFinset = 2 := by decide +kernel
lemma projection_inputs : projected toSmall 0 Large.inputs.toFinset = Small.inputs.toFinset := by decide +kernel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents Large.A C) : False := by
  obtain ⟨s, hs', hl⟩ := compress (build_mono_budget (Large.get_build C hm hr) hs)
  have e := Large.all_inputs hs' hl
  subst s
  have smaller := project_with_saving toSmall 0 Large.basicOps Small.basicOps Large.goal
    projection_nonzero toSmall_ops left_zero right_zero same_word hl
  rw [projection_goal, projection_saves, projection_inputs] at smaller
  exact Small.no_small smaller

end PEqualNP.Outside.L_meta_9460

theorem PEqualNP.Outside.L_meta_9460 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7580827 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_9460.no_small C hm hs hr
