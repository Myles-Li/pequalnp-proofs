import Mathlib
import PEqualNP.Defs

-- The lowerDag verifier engine is adapted from lean/PEqualNP/Outside/L_meta_8503.lean
-- in this repository, with the namespace renamed; the subproblem DAG and certificates
-- for L-meta-8515 are from its public source. The new row projections and gate certificates prove L-meta-8397.

namespace PEqualNP.Outside.L_meta_8397

abbrev Forest := Nat → Nat × Nat

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
abbrev CutCheck := RowState → Bool

def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])

def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

def childState (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep

abbrev Bound := Nat × List Word × Nat × Word

def stockWord (mask : Nat) (stock : List Word) (needed : List Word) (word : Word) : List Word :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Word) (history : List (Word × Word × Word)) :
    List Word :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Word) (w a b : Word) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp

theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Word} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : Bound} {bounds : List Bound}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Word} {bank : List Word}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Word} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Word}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Word)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Word}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b

theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]

variable {mask : Nat} {target : Word}

def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w

def wordWitness (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Word)} {z : Word} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha



def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw

theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all

def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b

theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩

theorem classifyWord {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega

def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem unaryChild {mask fuel a : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x : Word} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

theorem binaryChild {mask fuel a b : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]

def WordViable (mask : Nat) (target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Word} {U : Finset Word} {ws : List Word}
    {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : RowState := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Word}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Word) : Nat → Finset (Word) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Word} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Word} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m


def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m

theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

theorem flBoth {m a b : Word} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]

theorem simpleBin {m a b : Word} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]

def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))

theorem maskedBuild {goal : Word} {k t s} (run : LiveWord mask goal k t s) (m : Word) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Word} {v a b : Word}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

theorem buildsAppend {mask : Nat} {roots first second : List Word}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Word) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Word} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : RowState} {bound : Bound}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List Bound} {state : RowState}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

abbrev PointWire (rows : Nat) := Fin rows → Bool

def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : PointWire rows) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Word) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Word}
    {src dst : Word} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Word} {src dst : Word} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List Bound}
    {source destination : Bound} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Word) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
  ∃ f : Nat → Nat → Word,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)

theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)

theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩

namespace PackedRect

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2


theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

abbrev Witness := Word × Nat × Nat

def witnessWord (w : Witness) : Word := w.1

def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Word} {entry : Witness} {S : Finset Word} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Word} {witnesses : List Witness} {S : Finset Word} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Word} {witnesses : List Witness} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep

def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht

def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

abbrev RowChart := { rows : List Nat // rows.length = 24 }

def chartRow (chart : RowChart) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Word) (rows : List Nat) : Word :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Word) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : RowChart) (w : Word) : Word := chartBits w chart.val

def ChartOK (goal : Word) (chart : RowChart) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Word) (chart : Option RowChart) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Word} {chart : Option RowChart}
    (ok : chartCheck goal chart = true) (c : RowChart) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : RowChart) (w : Word) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Word} {chart : RowChart} {ws : List Word}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Word} {chart : RowChart} {ws : List Word} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Word).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Word) (state : RowState) (bound : Bound) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Word) (bounds : List Bound) (state : RowState) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]

abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink

def dagAllowedRoot (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Word) (stock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def dagRef (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1

def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Word} {ws : List Word} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same

abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word

def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : DagSample) (full : Word) (normal tight : DagCounts)
    (x y out : DagSignals) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Word} {ws : List Word} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Word) (chart : Option RowChart)
    (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Word) (op keep x y : Nat) : List Word :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Word) : Word :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl

abbrev DagTagged := Word × DagSignals

def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Word :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Word) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (links : DagLinks)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (stock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : RowState}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Word).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {ref : Nat → RowState → Bool} {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

theorem childStateData {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other

def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w

abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)

def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

theorem dagLinked {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem dagAllNodes {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {cut : CutCheck} {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    {bounds : List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    DagLinks := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option DagLink) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array WordMoveStep) (indices : List Nat) : WordMove :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Word}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let y : Fin n → Bool := fun k => j.testBit k.val
    have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
      beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hfg : goal.getLsbD j = f y :=
      beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
    have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn y)).getD C.output false = f y at hevj
    rw [← hbank, ← hbits] at hevj
    rw [hfg, ← hevj, ← hcsGetDBit]
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def moveStage0 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def moveStage1 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def moveStage2 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def moveStage3 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def moveStage4 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def moveStage5 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def moveStage6 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def moveStage7 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def moveStage8 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def moveStage9 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def moveStage10 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def moveStage11 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def moveStage12 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def moveStage13 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def moveStage14 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def moveStages : Array WordMoveStep := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11, moveStage12, moveStage13, moveStage14]
def sBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def sGoal : Word := 0xffffffffffffffffffffffffffeaeae8ffeeeeeeffeeeeecffeaeaeaffeaeae8
-- s0: K3_012 (lb=4, vars=3, kind=2)
def s0Mask : Word := 0xff
abbrev s0Goal : Word := sGoal &&& s0Mask
abbrev s0StockWords : List Word := projectDAGStock s0Mask sBase [0, 1, 2]
def s0Fact : Bound := (s0Mask, s0StockWords, 4, s0Goal)
def s0Witnesses := unpackWitnesses s0StockWords [1538, 263681, 526849]
def s0Cuts : List Bound := []
def s0Chart : Option RowChart := some ⟨[3, 5, 6, 7, 3, 5, 6, 7, 3, 5, 6, 7, 1, 2, 4, 0, 1, 2, 4, 0, 1, 2, 4, 0], rfl⟩
def s0Sample : DagSample := (0x201802050100c0406020140203, 6)
def s0Links : DagLinks :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 4
def s0Data : Forest := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x36b5b 0x22311 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (DagMoveRecord 256) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 256 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 1 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 3 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 1 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 8 s0RootAt = true := by decide +kernel
theorem s0RootVerified : treeBlock 0 8 s0RootAt = true := s0RootBlock0
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := s0RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Verified : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Verified
theorem s0Known : Known s0Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s0StockWords; decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s1: K3_034 (lb=4, vars=3, kind=2)
def s1Mask : Word := 0x3030303
abbrev s1Goal : Word := sGoal &&& s1Mask
abbrev s1StockWords : List Word := projectDAGStock s1Mask sBase [0, 3, 4]
def s1Fact : Bound := (s1Mask, s1StockWords, 4, s1Goal)
def s1Witnesses := unpackWitnesses s1StockWords [4616, 266753, 532993]
def s1Cuts : List Bound := []
def s1Chart : Option RowChart := some ⟨[9, 17, 24, 25, 9, 17, 24, 25, 9, 17, 24, 25, 1, 8, 16, 0, 1, 8, 16, 0, 1, 8, 16, 0], rfl⟩
def s1Sample : DagSample := (0x80600211040241018080440209, 6)
def s1Links : DagLinks :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 4
def s1Data : Forest := fun i => decodeNode 1 4 0xe i
def s1Tags := dagTraceTags s1Mask 6 (dagTagBases s1StockWords 0x36b5b 0x22311 6) 3 s1Data
def s1States := dagTrace s1Mask s1StockWords 3 s1Data
def s1MoveCert : List (DagMoveRecord 256) := []
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 256 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) 1 s1States s1Moves s1Links s1Sample s1Tags
def s1RootAt (token : Nat) : Bool :=
  let s := rootState s1StockWords 3 token
  !dagAllowedRoot s1Witnesses s.2.1 || dagLocal s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s ||
  dagRef 1 s1States s1Moves s1Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1RootBlock0 : treeBlock 0 8 s1RootAt = true := by decide +kernel
theorem s1RootVerified : treeBlock 0 8 s1RootAt = true := s1RootBlock0
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 1 s1States s1Moves s1Links 0) s1StockWords 3 = true := s1RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Block0 : treeBlock 0 1 s1Check = true := by decide +kernel
theorem s1Verified : treeBlock 0 1 s1Check = true := s1Block0
theorem s1Blocks : treeBlock 0 1 s1Check = true := s1Verified
theorem s1Known : Known s1Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := by
  apply lowerDag _ _ _ _ s1Autos _ _ _ s1Known _ s1Roots s1Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s1StockWords; decide +kernel
  · decide +kernel
  · simp only [s1Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s2: P4_1675 (lb=4, vars=4, kind=2)
def s2Mask : Word := 0x500000005000000050000000500000005000000050000000500000005
abbrev s2Goal : Word := sGoal &&& s2Mask
abbrev s2StockWords : List Word := projectDAGStock s2Mask sBase [1, 5, 6, 7]
def s2Fact : Bound := (s2Mask, s2StockWords, 4, s2Goal)
def s2Witnesses := unpackWitnesses s2StockWords [33856, 344192, 558082, 868384]
def s2Cuts : List Bound := []
def s2Chart : Option RowChart := some ⟨[66, 160, 192, 98, 162, 194, 224, 226, 66, 160, 192, 98, 34, 96, 130, 2, 32, 64, 128, 0, 34, 96, 130, 2], rfl⟩
def s2Sample : DagSample := (0x42, 1)
def s2Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 2 3
def s2Data : Forest := fun i => decodeNode 1 5 0x0 i
def s2Tags := dagTraceTags s2Mask 1 (dagTagBases s2StockWords 0x5 0x0 1) 3 s2Data
def s2States := dagTrace s2Mask s2StockWords 3 s2Data
def s2MoveCert : List (DagMoveRecord 256) := []
def s2Moves := dagMoves s2MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Autos : DagMovesOK s2Mask s2Goal 256 s2Moves := dagMovesOfCheck (by decide +kernel)
def s2Check := dagCheckNode s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) 0 s2States s2Moves s2Links s2Sample s2Tags
def s2RootAt (token : Nat) : Bool :=
  let s := rootState s2StockWords 3 token
  !dagAllowedRoot s2Witnesses s.2.1 || dagLocal s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s ||
  dagRef 0 s2States s2Moves s2Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2RootBlock0 : treeBlock 0 16 s2RootAt = true := by decide +kernel
theorem s2RootVerified : treeBlock 0 16 s2RootAt = true := s2RootBlock0
theorem s2Roots : dagCheckRoots s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s2Witnesses (dagRef 0 s2States s2Moves s2Links 0) s2StockWords 3 = true := s2RootVerified
theorem s2Blocks : treeBlock 0 0 s2Check = true := rfl
theorem s2Known : Known s2Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := by
  apply lowerDag _ _ _ _ s2Autos _ _ _ s2Known _ s2Roots s2Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s2StockWords; decide +kernel
  · decide +kernel
  · simp only [s2Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s3: P5_21675 (lb=5, vars=5, kind=1)
def s3Mask : Word := 0x5500000055000000550000005500000055000000550000005500000055
abbrev s3Goal : Word := sGoal &&& s3Mask
abbrev s3StockWords : List Word := projectDAGStock s3Mask sBase [1, 2, 5, 6, 7]
def s3Fact : Bound := (s3Mask, s3StockWords, 5, s3Goal)
def s3Witnesses := unpackWitnesses s3StockWords [3076, 265218, 606336, 820226, 1130528]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 5 := by
  apply essentialLift (witnesses := s3Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
-- s4: C5_1=0 (lb=4, vars=4, kind=2)
def s4Mask : Word := 0x300000003000000030000000300000003000000030000000300000003
abbrev s4Goal : Word := sGoal &&& s4Mask
abbrev s4StockWords : List Word := projectDAGStock s4Mask sBase [0, 5, 6, 7]
def s4Fact : Bound := (s4Mask, s4StockWords, 4, s4Goal)
def s4Witnesses := unpackWitnesses s4StockWords [16928, 279041, 622720, 868384]
def s4Cuts : List Bound := []
def s4Chart : Option RowChart := some ⟨[33, 160, 192, 97, 161, 193, 224, 225, 33, 160, 192, 97, 65, 96, 129, 1, 32, 64, 128, 0, 65, 96, 129, 1], rfl⟩
def s4Sample : DagSample := (0x21, 1)
def s4Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 3 3
def s4Data : Forest := fun i => decodeNode 1 5 0x0 i
def s4Tags := dagTraceTags s4Mask 1 (dagTagBases s4StockWords 0x3 0x0 1) 3 s4Data
def s4States := dagTrace s4Mask s4StockWords 3 s4Data
def s4MoveCert : List (DagMoveRecord 256) := []
def s4Moves := dagMoves s4MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Autos : DagMovesOK s4Mask s4Goal 256 s4Moves := dagMovesOfCheck (by decide +kernel)
def s4Check := dagCheckNode s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) 0 s4States s4Moves s4Links s4Sample s4Tags
def s4RootAt (token : Nat) : Bool :=
  let s := rootState s4StockWords 3 token
  !dagAllowedRoot s4Witnesses s.2.1 || dagLocal s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s ||
  dagRef 0 s4States s4Moves s4Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4RootBlock0 : treeBlock 0 16 s4RootAt = true := by decide +kernel
theorem s4RootVerified : treeBlock 0 16 s4RootAt = true := s4RootBlock0
theorem s4Roots : dagCheckRoots s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s4Witnesses (dagRef 0 s4States s4Moves s4Links 0) s4StockWords 3 = true := s4RootVerified
theorem s4Blocks : treeBlock 0 0 s4Check = true := rfl
theorem s4Known : Known s4Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := by
  apply lowerDag _ _ _ _ s4Autos _ _ _ s4Known _ s4Roots s4Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s4StockWords; decide +kernel
  · decide +kernel
  · simp only [s4Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s5: C5_5=0 (lb=4, vars=4, kind=2)
def s5Mask : Word := 0xf000000000000000f000000000000000f000000000000000f
abbrev s5Goal : Word := sGoal &&& s5Mask
abbrev s5StockWords : List Word := projectDAGStock s5Mask sBase [0, 1, 6, 7]
def s5Fact : Bound := (s5Mask, s5StockWords, 4, s5Goal)
def s5Witnesses := unpackWitnesses s5StockWords [1538, 263681, 558082, 884800]
def s5Cuts : List Bound := []
def s5Chart : Option RowChart := some ⟨[3, 66, 192, 67, 131, 193, 194, 195, 3, 66, 192, 67, 65, 129, 130, 1, 2, 64, 128, 0, 65, 129, 130, 1], rfl⟩
def s5Sample : DagSample := (0x3, 1)
def s5Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s5Data : Forest := fun i => decodeNode 1 5 0x0 i
def s5Tags := dagTraceTags s5Mask 1 (dagTagBases s5StockWords 0x3 0x0 1) 3 s5Data
def s5States := dagTrace s5Mask s5StockWords 3 s5Data
def s5MoveCert : List (DagMoveRecord 256) := []
def s5Moves := dagMoves s5MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Autos : DagMovesOK s5Mask s5Goal 256 s5Moves := dagMovesOfCheck (by decide +kernel)
def s5Check := dagCheckNode s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) 0 s5States s5Moves s5Links s5Sample s5Tags
def s5RootAt (token : Nat) : Bool :=
  let s := rootState s5StockWords 3 token
  !dagAllowedRoot s5Witnesses s.2.1 || dagLocal s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) s ||
  dagRef 0 s5States s5Moves s5Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5RootBlock0 : treeBlock 0 16 s5RootAt = true := by decide +kernel
theorem s5RootVerified : treeBlock 0 16 s5RootAt = true := s5RootBlock0
theorem s5Roots : dagCheckRoots s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) s5Witnesses (dagRef 0 s5States s5Moves s5Links 0) s5StockWords 3 = true := s5RootVerified
theorem s5Blocks : treeBlock 0 0 s5Check = true := rfl
theorem s5Known : Known s5Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := by
  apply lowerDag _ _ _ _ s5Autos _ _ _ s5Known _ s5Roots s5Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s5StockWords; decide +kernel
  · decide +kernel
  · simp only [s5Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s6: C5_6=0 (lb=4, vars=4, kind=2)
def s6Mask : Word := 0xf0000000f00000000000000000000000f0000000f
abbrev s6Goal : Word := sGoal &&& s6Mask
abbrev s6StockWords : List Word := projectDAGStock s6Mask sBase [0, 1, 5, 7]
def s6Fact : Bound := (s6Mask, s6StockWords, 4, s6Goal)
def s6Witnesses := unpackWitnesses s6StockWords [1538, 263681, 541185, 868384]
def s6Cuts : List Bound := []
def s6Chart : Option RowChart := some ⟨[3, 33, 160, 35, 131, 161, 162, 163, 3, 33, 160, 35, 34, 129, 130, 1, 2, 32, 128, 0, 34, 129, 130, 1], rfl⟩
def s6Sample : DagSample := (0x3, 1)
def s6Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s6Data : Forest := fun i => decodeNode 1 5 0x0 i
def s6Tags := dagTraceTags s6Mask 1 (dagTagBases s6StockWords 0x3 0x0 1) 3 s6Data
def s6States := dagTrace s6Mask s6StockWords 3 s6Data
def s6MoveCert : List (DagMoveRecord 256) := []
def s6Moves := dagMoves s6MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Autos : DagMovesOK s6Mask s6Goal 256 s6Moves := dagMovesOfCheck (by decide +kernel)
def s6Check := dagCheckNode s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) 0 s6States s6Moves s6Links s6Sample s6Tags
def s6RootAt (token : Nat) : Bool :=
  let s := rootState s6StockWords 3 token
  !dagAllowedRoot s6Witnesses s.2.1 || dagLocal s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s ||
  dagRef 0 s6States s6Moves s6Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6RootBlock0 : treeBlock 0 16 s6RootAt = true := by decide +kernel
theorem s6RootVerified : treeBlock 0 16 s6RootAt = true := s6RootBlock0
theorem s6Roots : dagCheckRoots s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s6Witnesses (dagRef 0 s6States s6Moves s6Links 0) s6StockWords 3 = true := s6RootVerified
theorem s6Blocks : treeBlock 0 0 s6Check = true := rfl
theorem s6Known : Known s6Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 4 := by
  apply lowerDag _ _ _ _ s6Autos _ _ _ s6Known _ s6Roots s6Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s6StockWords; decide +kernel
  · decide +kernel
  · simp only [s6Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s7: C5_7=0 (lb=4, vars=4, kind=2)
def s7Mask : Word := 0xf0000000f0000000f0000000f
abbrev s7Goal : Word := sGoal &&& s7Mask
abbrev s7StockWords : List Word := projectDAGStock s7Mask sBase [0, 1, 5, 6]
def s7Fact : Bound := (s7Mask, s7StockWords, 4, s7Goal)
def s7Witnesses := unpackWitnesses s7StockWords [1538, 263681, 541185, 820226]
def s7Cuts : List Bound := []
def s7Chart : Option RowChart := some ⟨[3, 33, 66, 35, 67, 97, 98, 99, 3, 33, 66, 35, 34, 65, 96, 1, 2, 32, 64, 0, 34, 65, 96, 1], rfl⟩
def s7Sample : DagSample := (0x3, 1)
def s7Links : DagLinks :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 3
def s7Data : Forest := fun i => decodeNode 1 5 0x0 i
def s7Tags := dagTraceTags s7Mask 1 (dagTagBases s7StockWords 0x3 0x0 1) 3 s7Data
def s7States := dagTrace s7Mask s7StockWords 3 s7Data
def s7MoveCert : List (DagMoveRecord 256) := []
def s7Moves := dagMoves s7MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Autos : DagMovesOK s7Mask s7Goal 256 s7Moves := dagMovesOfCheck (by decide +kernel)
def s7Check := dagCheckNode s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) 0 s7States s7Moves s7Links s7Sample s7Tags
def s7RootAt (token : Nat) : Bool :=
  let s := rootState s7StockWords 3 token
  !dagAllowedRoot s7Witnesses s.2.1 || dagLocal s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s ||
  dagRef 0 s7States s7Moves s7Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7RootBlock0 : treeBlock 0 16 s7RootAt = true := by decide +kernel
theorem s7RootVerified : treeBlock 0 16 s7RootAt = true := s7RootBlock0
theorem s7Roots : dagCheckRoots s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s7Witnesses (dagRef 0 s7States s7Moves s7Links 0) s7StockWords 3 = true := s7RootVerified
theorem s7Blocks : treeBlock 0 0 s7Check = true := rfl
theorem s7Known : Known s7Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 4 := by
  apply lowerDag _ _ _ _ s7Autos _ _ _ s7Known _ s7Roots s7Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s7StockWords; decide +kernel
  · decide +kernel
  · simp only [s7Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
-- s8: C5 (lb=7, vars=5, kind=2)
def s8Mask : Word := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
abbrev s8Goal : Word := sGoal &&& s8Mask
abbrev s8StockWords : List Word := projectDAGStock s8Mask sBase [0, 1, 5, 6, 7]
def s8Fact : Bound := (s8Mask, s8StockWords, 7, s8Goal)
def s8Witnesses := unpackWitnesses s8StockWords [1538, 263681, 541185, 820226, 1130528]
def s8Cuts : List Bound := [s2Fact, s4Fact, s5Fact, s6Fact, s7Fact]
def s8Chart : Option RowChart := some ⟨[3, 33, 66, 160, 192, 35, 67, 97, 98, 131, 161, 162, 34, 65, 96, 129, 130, 1, 2, 32, 64, 128, 0, 34], rfl⟩
def s8Sample : DagSample := (0x2030088440a01110844a02010880c02080c82c04028100c04110904a010084440311084822130084c04230189020340b0504034128844a230185022140a0d02a14120c824320b044423111888261, 35)
def s8Links : DagLinks :=
  dagLookupLinks 0x30c30341 0x7c38392c662023141008001f 6 3 12 2 2 5
def s8Data : Forest := fun i => decodeNode 3 15 0x92c2628402080f8 i
def s8Tags := dagTraceTags s8Mask 35 (dagTagBases s8StockWords 0x157402ce816b034436d09ba3d1e5448ee5b6083e73fd 0x3c079e00780f0432700ee1818606c0e1360c0461d9 35) 6 s8Data
def s8States := dagTrace s8Mask s8StockWords 6 s8Data
def s8Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 3, 4, 1, 7, 6] 0 i.val)
def s8MoveCert : List (DagMoveRecord 256) := [([([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)]), ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])], s8Move1Map, s8Move1Map)]
def s8Moves := dagMoves s8MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Autos : DagMovesOK s8Mask s8Goal 256 s8Moves := dagMovesOfCheck (by decide +kernel)
def s8Check := dagCheckNode s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) 4 s8States s8Moves s8Links s8Sample s8Tags
def s8RootAt (token : Nat) : Bool :=
  let s := rootState s8StockWords 6 token
  !dagAllowedRoot s8Witnesses s.2.1 || dagLocal s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) s ||
  dagRef 4 s8States s8Moves s8Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8RootBlock0 : treeBlock 0 32 s8RootAt = true := by decide +kernel
theorem s8RootVerified : treeBlock 0 32 s8RootAt = true := s8RootBlock0
theorem s8Roots : dagCheckRoots s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) s8Witnesses (dagRef 4 s8States s8Moves s8Links 0) s8StockWords 6 = true := s8RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Block0 : treeBlock 0 4 s8Check = true := by decide +kernel
theorem s8Verified : treeBlock 0 4 s8Check = true := s8Block0
theorem s8Blocks : treeBlock 0 4 s8Check = true := s8Verified
theorem s8Known : Known s8Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s6Stock) s5Stock) s4Stock) s2Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 7 := by
  apply lowerDag _ _ _ _ s8Autos _ _ _ s8Known _ s8Roots s8Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s8StockWords; decide +kernel
  · decide +kernel
  · simp only [s8Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s9: BT_3=0 (lb=5, vars=4, kind=1)
def s9Mask : Word := 0xff00ff
abbrev s9Goal : Word := sGoal &&& s9Mask
abbrev s9StockWords : List Word := projectDAGStock s9Mask sBase [0, 1, 2, 4]
def s9Fact : Bound := (s9Mask, s9StockWords, 5, s9Goal)
def s9Witnesses := unpackWitnesses s9StockWords [1538, 263681, 526849, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 5 := by
  apply essentialLift (witnesses := s9Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s10: BT_4=0 (lb=5, vars=4, kind=1)
def s10Mask : Word := 0xffff
abbrev s10Goal : Word := sGoal &&& s10Mask
abbrev s10StockWords : List Word := projectDAGStock s10Mask sBase [0, 1, 2, 3]
def s10Fact : Bound := (s10Mask, s10StockWords, 5, s10Goal)
def s10Witnesses := unpackWitnesses s10StockWords [1538, 263681, 526849, 791041]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := by
  apply essentialLift (witnesses := s10Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s11: BT_1=0 (lb=5, vars=4, kind=1)
def s11Mask : Word := 0x33333333
abbrev s11Goal : Word := sGoal &&& s11Mask
abbrev s11StockWords : List Word := projectDAGStock s11Mask sBase [0, 2, 3, 4]
def s11Fact : Bound := (s11Mask, s11StockWords, 5, s11Goal)
def s11Witnesses := unpackWitnesses s11StockWords [2564, 264705, 528897, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := by
  apply essentialLift (witnesses := s11Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s12: BT_2=0 (lb=5, vars=4, kind=1)
def s12Mask : Word := 0xf0f0f0f
abbrev s12Goal : Word := sGoal &&& s12Mask
abbrev s12StockWords : List Word := projectDAGStock s12Mask sBase [0, 1, 3, 4]
def s12Fact : Bound := (s12Mask, s12StockWords, 5, s12Goal)
def s12Witnesses := unpackWitnesses s12StockWords [1538, 263681, 528897, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 5 := by
  apply essentialLift (witnesses := s12Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s13: BT_0=0 (lb=3, vars=4, kind=0)
def s13Mask : Word := 0x55555555
abbrev s13Goal : Word := sGoal &&& s13Mask
abbrev s13StockWords : List Word := projectDAGStock s13Mask sBase [1, 2, 3, 4]
def s13Fact : Bound := (s13Mask, s13StockWords, 3, s13Goal)
def s13Witnesses := unpackWitnesses s13StockWords [3076, 265218, 536592, 798728]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 3 := by
  apply essentialLower (witnesses := s13Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s14: BT_1=1 (lb=3, vars=4, kind=0)
def s14Mask : Word := 0xcccccccc
abbrev s14Goal : Word := sGoal &&& s14Mask
abbrev s14StockWords : List Word := projectDAGStock s14Mask sBase [0, 2, 3, 4]
def s14Fact : Bound := (s14Mask, s14StockWords, 3, s14Goal)
def s14Witnesses := unpackWitnesses s14StockWords [1538, 265218, 537618, 799754]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 3 := by
  apply essentialLower (witnesses := s14Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s15: BT_2=1 (lb=3, vars=4, kind=0)
def s15Mask : Word := 0xf0f0f0f0
abbrev s15Goal : Word := sGoal &&& s15Mask
abbrev s15StockWords : List Word := projectDAGStock s15Mask sBase [0, 1, 3, 4]
def s15Fact : Bound := (s15Mask, s15StockWords, 3, s15Goal)
def s15Witnesses := unpackWitnesses s15StockWords [2564, 265220, 538644, 800780]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 3 := by
  apply essentialLower (witnesses := s15Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s16: BT_3=1 (lb=3, vars=4, kind=0)
def s16Mask : Word := 0xff00ff00
abbrev s16Goal : Word := sGoal &&& s16Mask
abbrev s16StockWords : List Word := projectDAGStock s16Mask sBase [0, 1, 2, 4]
def s16Fact : Bound := (s16Mask, s16StockWords, 3, s16Goal)
def s16Witnesses := unpackWitnesses s16StockWords [4616, 269324, 531466, 798728]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 3 := by
  apply essentialLower (witnesses := s16Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s17: BT_4=1 (lb=3, vars=4, kind=0)
def s17Mask : Word := 0xffff0000
abbrev s17Goal : Word := sGoal &&& s17Mask
abbrev s17StockWords : List Word := projectDAGStock s17Mask sBase [0, 1, 2, 3]
def s17Fact : Bound := (s17Mask, s17StockWords, 3, s17Goal)
def s17Witnesses := unpackWitnesses s17StockWords [8720, 273428, 535570, 798736]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 3 := by
  apply essentialLower (witnesses := s17Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s18: BOWTIE (lb=8, vars=5, kind=2)
def s18Mask : Word := 0xffffffff
abbrev s18Goal : Word := sGoal &&& s18Mask
abbrev s18StockWords : List Word := projectDAGStock s18Mask sBase [0, 1, 2, 3, 4]
def s18Fact : Bound := (s18Mask, s18StockWords, 8, s18Goal)
def s18Witnesses := unpackWitnesses s18StockWords [1538, 263681, 526849, 791041, 1057281]
def s18Cuts : List Bound := [s9Fact, s10Fact, s11Fact, s12Fact, s13Fact, s14Fact, s15Fact, s16Fact, s17Fact]
def s18Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 7, 11, 13, 14, 19, 21, 10, 12, 18, 20, 1, 2, 4, 8, 16, 0, 10, 12], rfl⟩
def s18Sample : DagSample := (0x8050402c14180601420180a044100d0606020110a01428180406014090602428150402414030900c28060601824160a05814060904c180d09018281c0080c181c00844180e0906802050502c020905038141a, 37)
def s18Links : DagLinks :=
  dagLookupLinks 0x320c8320c8320a92a0a82240c001 0x19c381325821880398a57c388f2589d880398a54c388b26f124b1b31ba662b48c4058cdc31958531f086294c0de1815a301f060260802408040001f 10 5 12 4 3 7
def s18Data : Forest := fun i => decodeNode 4 16 0x92c56205314232b131f1314101310091008101f0 i
def s18Tags := dagTraceTags s18Mask 37 (dagTagBases s18StockWords 0x5b641a5a16b3d00ab7c9211f75490003fd4d7ad9f8329c 0x19c4dac20731d928a5cab31a550080232d056000000294 37) 7 s18Data
def s18States := dagTrace s18Mask s18StockWords 7 s18Data
def s18Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s18Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s18Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s18Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 1, 2, 5, 6, 7] 0 i.val)
def s18Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 3, 2, 1, 5, 6, 7] 0 i.val)
def s18MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s18Move0Map, s18Move0Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s18Move1Map, s18Move1Map), ([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)]), ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s18Move2Map, s18Move2Map), ([([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)]), ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])], s18Move3Map, s18Move3Map), ([([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)]), ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])], s18Move4Map, s18Move4Map)]
def s18Moves := dagMoves s18MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Autos : DagMovesOK s18Mask s18Goal 256 s18Moves := dagMovesOfCheck (by decide +kernel)
def s18Check := dagCheckNode s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) 10 s18States s18Moves s18Links s18Sample s18Tags
def s18RootAt (token : Nat) : Bool :=
  let s := rootState s18StockWords 7 token
  !dagAllowedRoot s18Witnesses s.2.1 || dagLocal s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s ||
  dagRef 10 s18States s18Moves s18Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18RootBlock0 : treeBlock 0 32 s18RootAt = true := by decide +kernel
theorem s18RootVerified : treeBlock 0 32 s18RootAt = true := s18RootBlock0
theorem s18Roots : dagCheckRoots s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s18Witnesses (dagRef 10 s18States s18Moves s18Links 0) s18StockWords 7 = true := s18RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block0 : treeBlock 0 10 s18Check = true := by decide +kernel
theorem s18Verified : treeBlock 0 10 s18Check = true := s18Block0
theorem s18Blocks : treeBlock 0 10 s18Check = true := s18Verified
theorem s18Known : Known s18Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock) s16Stock) s15Stock) s14Stock) s13Stock) s12Stock) s11Stock) s10Stock) s9Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 8 := by
  apply lowerDag _ _ _ _ s18Autos _ _ _ s18Known _ s18Roots s18Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s18StockWords; decide +kernel
  · decide +kernel
  · simp only [s18Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s19: K3_012_7=1 (lb=4, vars=3, kind=3)
def s19Mask : Word := 0xff00000000000000000000000000000000
abbrev s19Goal : Word := sGoal &&& s19Mask
abbrev s19StockWords : List Word := projectDAGStock s19Mask sBase [0, 1, 2]
def s19Fact : Bound := (s19Mask, s19StockWords, 4, s19Goal)
def s19Witnesses := unpackWitnesses s19StockWords [67202, 329345, 592513]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 4 := dagShiftLower (width := 256) [([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])] s0Stock (by decide +kernel)
-- s20: K3_034_7=1 (lb=4, vars=3, kind=3)
def s20Mask : Word := 0x303030300000000000000000000000000000000
abbrev s20Goal : Word := sGoal &&& s20Mask
abbrev s20StockWords : List Word := projectDAGStock s20Mask sBase [0, 3, 4]
def s20Fact : Bound := (s20Mask, s20StockWords, 4, s20Goal)
def s20Witnesses := unpackWitnesses s20StockWords [70280, 332417, 598657]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 4 := dagShiftLower (width := 256) [([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])] s1Stock (by decide +kernel)
-- s21: K3_034_6=1 (lb=4, vars=3, kind=3)
def s21Mask : Word := 0x30303030000000000000000
abbrev s21Goal : Word := sGoal &&& s21Mask
abbrev s21StockWords : List Word := projectDAGStock s21Mask sBase [0, 3, 4]
def s21Fact : Bound := (s21Mask, s21StockWords, 4, s21Goal)
def s21Witnesses := unpackWitnesses s21StockWords [37448, 299585, 565825]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 4 := dagShiftLower (width := 256) [([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])] s1Stock (by decide +kernel)
-- s22: P4_3=1 (lb=4, vars=4, kind=3)
def s22Mask : Word := 0x50000000500000005000000050000000500000005000000050000000500
abbrev s22Goal : Word := sGoal &&& s22Mask
abbrev s22StockWords : List Word := projectDAGStock s22Mask sBase [1, 5, 6, 7]
def s22Fact : Bound := (s22Mask, s22StockWords, 4, s22Goal)
def s22Witnesses := unpackWitnesses s22StockWords [37960, 348296, 562186, 872488]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 4 := dagShiftLower (width := 256) [([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])] s2Stock (by decide +kernel)
-- s27: 34_50_70 (lb=5, vars=4, kind=1)
def s27Mask : Word := 0xff00000000000000ff
abbrev s27Goal : Word := sGoal &&& s27Mask
abbrev s27StockWords : List Word := projectDAGStock s27Mask sBase [0, 1, 2, 6]
def s27Fact : Bound := (s27Mask, s27StockWords, 5, s27Goal)
def s27Witnesses := unpackWitnesses s27StockWords [1538, 263681, 526849, 820226]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := by
  apply essentialLift (witnesses := s27Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s28: 34_50_71 (lb=5, vars=4, kind=1)
def s28Mask : Word := 0xff00000000000000ff00000000000000000000000000000000
abbrev s28Goal : Word := sGoal &&& s28Mask
abbrev s28StockWords : List Word := projectDAGStock s28Mask sBase [0, 1, 2, 6]
def s28Fact : Bound := (s28Mask, s28StockWords, 5, s28Goal)
def s28Witnesses := unpackWitnesses s28StockWords [67202, 329345, 592513, 884864]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := by
  apply essentialLift (witnesses := s28Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
-- s29: 34_50 (lb=7, vars=5, kind=2)
def s29Mask : Word := 0xff00000000000000ff00000000000000ff00000000000000ff
abbrev s29Goal : Word := sGoal &&& s29Mask
abbrev s29StockWords : List Word := projectDAGStock s29Mask sBase [0, 1, 2, 6, 7]
def s29Fact : Bound := (s29Mask, s29StockWords, 7, s29Goal)
def s29Witnesses := unpackWitnesses s29StockWords [1538, 263681, 526849, 820226, 1146944]
def s29Cuts : List Bound := [s27Fact, s28Fact]
def s29Chart : Option RowChart := some ⟨[3, 5, 6, 66, 192, 7, 67, 69, 70, 131, 133, 134, 65, 68, 129, 130, 132, 1, 2, 4, 64, 128, 0, 65], rfl⟩
def s29Sample : DagSample := (0x2201902c04221908c04231080422080c82052090888052210908852211904c22090c884540a15048620915028340b050483, 22)
def s29Links : DagLinks :=
  dagLookupLinks 0xa28a28301 0x492c362023141008001f 6 3 12 3 1 5
def s29Data : Forest := fun i => decodeNode 3 15 0x49616202628402080f8 i
def s29Tags := dagTraceTags s29Mask 22 (dagTagBases s29StockWords 0x1e05375caf2aa5678a6ae540d4ef 0x1e053787eb22e1e400004450e0ae 22) 6 s29Data
def s29States := dagTrace s29Mask s29StockWords 6 s29Data
def s29MoveCert : List (DagMoveRecord 256) := []
def s29Moves := dagMoves s29MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Autos : DagMovesOK s29Mask s29Goal 256 s29Moves := dagMovesOfCheck (by decide +kernel)
def s29Check := dagCheckNode s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) 5 s29States s29Moves s29Links s29Sample s29Tags
def s29RootAt (token : Nat) : Bool :=
  let s := rootState s29StockWords 6 token
  !dagAllowedRoot s29Witnesses s.2.1 || dagLocal s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s ||
  dagRef 5 s29States s29Moves s29Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29RootBlock0 : treeBlock 0 32 s29RootAt = true := by decide +kernel
theorem s29RootVerified : treeBlock 0 32 s29RootAt = true := s29RootBlock0
theorem s29Roots : dagCheckRoots s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s29Witnesses (dagRef 5 s29States s29Moves s29Links 0) s29StockWords 6 = true := s29RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block0 : treeBlock 0 5 s29Check = true := by decide +kernel
theorem s29Verified : treeBlock 0 5 s29Check = true := s29Block0
theorem s29Blocks : treeBlock 0 5 s29Check = true := s29Verified
theorem s29Known : Known s29Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s28Stock) s27Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 7 := by
  apply lowerDag _ _ _ _ s29Autos _ _ _ s29Known _ s29Roots s29Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s29StockWords; decide +kernel
  · decide +kernel
  · simp only [s29Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s30: 34_60_70 (lb=5, vars=4, kind=1)
def s30Mask : Word := 0xff000000ff
abbrev s30Goal : Word := sGoal &&& s30Mask
abbrev s30StockWords : List Word := projectDAGStock s30Mask sBase [0, 1, 2, 5]
def s30Fact : Bound := (s30Mask, s30StockWords, 5, s30Goal)
def s30Witnesses := unpackWitnesses s30StockWords [1538, 263681, 526849, 803329]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 5 := by
  apply essentialLift (witnesses := s30Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s31: 34_60_71 (lb=5, vars=4, kind=1)
def s31Mask : Word := 0xff000000ff00000000000000000000000000000000
abbrev s31Goal : Word := sGoal &&& s31Mask
abbrev s31StockWords : List Word := projectDAGStock s31Mask sBase [0, 1, 2, 5]
def s31Fact : Bound := (s31Mask, s31StockWords, 5, s31Goal)
def s31Witnesses := unpackWitnesses s31StockWords [67202, 329345, 592513, 868480]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := by
  apply essentialLift (witnesses := s31Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
-- s32: 34_60 (lb=7, vars=5, kind=2)
def s32Mask : Word := 0xff000000ff0000000000000000000000ff000000ff
abbrev s32Goal : Word := sGoal &&& s32Mask
abbrev s32StockWords : List Word := projectDAGStock s32Mask sBase [0, 1, 2, 5, 7]
def s32Fact : Bound := (s32Mask, s32StockWords, 7, s32Goal)
def s32Witnesses := unpackWitnesses s32StockWords [1538, 263681, 526849, 803329, 1130528]
def s32Cuts : List Bound := [s30Fact, s31Fact]
def s32Chart : Option RowChart := some ⟨[3, 5, 6, 33, 160, 7, 35, 37, 38, 131, 133, 134, 34, 36, 129, 130, 132, 1, 2, 4, 32, 128, 0, 34], rfl⟩
def s32Sample : DagSample := (0x40211100c44211201508864228108a41101848061208504864221504a21108c48251209904831109902a140a150283, 21)
def s32Links : DagLinks :=
  dagLookupLinks 0x28a28301 0x392c662023141008001f 6 3 12 2 2 5
def s32Data : Forest := fun i => decodeNode 3 15 0x92c2628402080f8 i
def s32Tags := dagTraceTags s32Mask 21 (dagTagBases s32StockWords 0x1c717a64f60dd9a926b73e0ad7 0x1c717f1c740f698184b3000007 21) 6 s32Data
def s32States := dagTrace s32Mask s32StockWords 6 s32Data
def s32Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s32MoveCert : List (DagMoveRecord 256) := [([([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])], s32Move1Map, s32Move1Map)]
def s32Moves := dagMoves s32MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Autos : DagMovesOK s32Mask s32Goal 256 s32Moves := dagMovesOfCheck (by decide +kernel)
def s32Check := dagCheckNode s32Mask s32Goal s32Chart (dagKnownCloses s32Goal s32Cuts) 4 s32States s32Moves s32Links s32Sample s32Tags
def s32RootAt (token : Nat) : Bool :=
  let s := rootState s32StockWords 6 token
  !dagAllowedRoot s32Witnesses s.2.1 || dagLocal s32Mask s32Goal s32Chart (dagKnownCloses s32Goal s32Cuts) s ||
  dagRef 4 s32States s32Moves s32Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32RootBlock0 : treeBlock 0 32 s32RootAt = true := by decide +kernel
theorem s32RootVerified : treeBlock 0 32 s32RootAt = true := s32RootBlock0
theorem s32Roots : dagCheckRoots s32Mask s32Goal s32Chart (dagKnownCloses s32Goal s32Cuts) s32Witnesses (dagRef 4 s32States s32Moves s32Links 0) s32StockWords 6 = true := s32RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Block0 : treeBlock 0 4 s32Check = true := by decide +kernel
theorem s32Verified : treeBlock 0 4 s32Check = true := s32Block0
theorem s32Blocks : treeBlock 0 4 s32Check = true := s32Verified
theorem s32Known : Known s32Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s31Stock) s30Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 7 := by
  apply lowerDag _ _ _ _ s32Autos _ _ _ s32Known _ s32Roots s32Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s32StockWords; decide +kernel
  · decide +kernel
  · simp only [s32Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s33: 34_70 (lb=6, vars=5, kind=1)
def s33Mask : Word := 0xff000000ff000000ff000000ff
abbrev s33Goal : Word := sGoal &&& s33Mask
abbrev s33StockWords : List Word := projectDAGStock s33Mask sBase [0, 1, 2, 5, 6]
def s33Fact : Bound := (s33Mask, s33StockWords, 6, s33Goal)
def s33Witnesses := unpackWitnesses s33StockWords [1538, 263681, 526849, 803329, 1082370]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 6 := by
  apply essentialLift (witnesses := s33Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
-- s34: 34_71 (lb=6, vars=5, kind=1)
def s34Mask : Word := 0xff000000ff000000ff000000ff00000000000000000000000000000000
abbrev s34Goal : Word := sGoal &&& s34Mask
abbrev s34StockWords : List Word := projectDAGStock s34Mask sBase [0, 1, 2, 5, 6]
def s34Fact : Bound := (s34Mask, s34StockWords, 6, s34Goal)
def s34Witnesses := unpackWitnesses s34StockWords [67202, 329345, 592513, 868480, 1147008]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 6 := by
  apply essentialLift (witnesses := s34Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
-- s35: 34_10 (lb=5, vars=5, kind=1)
def s35Mask : Word := 0x3300000033000000330000003300000033000000330000003300000033
abbrev s35Goal : Word := sGoal &&& s35Mask
abbrev s35StockWords : List Word := projectDAGStock s35Mask sBase [0, 2, 5, 6, 7]
def s35Fact : Bound := (s35Mask, s35StockWords, 5, s35Goal)
def s35Witnesses := unpackWitnesses s35StockWords [2564, 264705, 541185, 884864, 1130528]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 5 := by
  apply essentialLift (witnesses := s35Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
-- s36: 34_51 (lb=4, vars=5, kind=0)
def s36Mask : Word := 0xff00000000000000ff00000000000000ff00000000000000ff00000000
abbrev s36Goal : Word := sGoal &&& s36Mask
abbrev s36StockWords : List Word := projectDAGStock s36Mask sBase [0, 1, 2, 6, 7]
def s36Fact : Bound := (s36Mask, s36StockWords, 4, s36Goal)
def s36Witnesses := unpackWitnesses s36StockWords [16928, 281636, 543778, 836642, 1130528]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 4 := by
  apply essentialLower (witnesses := s36Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s37: 34_61 (lb=4, vars=5, kind=0)
def s37Mask : Word := 0xff000000ff0000000000000000000000ff000000ff0000000000000000
abbrev s37Goal : Word := sGoal &&& s37Mask
abbrev s37StockWords : List Word := projectDAGStock s37Mask sBase [0, 1, 2, 5, 7]
def s37Fact : Bound := (s37Mask, s37StockWords, 4, s37Goal)
def s37Witnesses := unpackWitnesses s37StockWords [35396, 296000, 559681, 836161, 1146944]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 4 := by
  apply essentialLower (witnesses := s37Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s38: 34_21 (lb=4, vars=5, kind=0)
def s38Mask : Word := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0
abbrev s38Goal : Word := sGoal &&& s38Mask
abbrev s38StockWords : List Word := projectDAGStock s38Mask sBase [0, 1, 5, 6, 7]
def s38Fact : Bound := (s38Mask, s38StockWords, 4, s38Goal)
def s38Witnesses := unpackWitnesses s38StockWords [2564, 265220, 608388, 886916, 1132580]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 4 := by
  apply essentialLower (witnesses := s38Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s39: 34_01 (lb=4, vars=5, kind=0)
def s39Mask : Word := 0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
abbrev s39Goal : Word := sGoal &&& s39Mask
abbrev s39StockWords : List Word := projectDAGStock s39Mask sBase [1, 2, 5, 6, 7]
def s39Fact : Bound := (s39Mask, s39StockWords, 4, s39Goal)
def s39Witnesses := unpackWitnesses s39StockWords [1537, 264705, 541185, 885377, 1147457]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 4 := by
  apply essentialLower (witnesses := s39Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s40: 34_11 (lb=4, vars=5, kind=0)
def s40Mask : Word := 0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc
abbrev s40Goal : Word := sGoal &&& s40Mask
abbrev s40StockWords : List Word := projectDAGStock s40Mask sBase [0, 2, 5, 6, 7]
def s40Fact : Bound := (s40Mask, s40StockWords, 4, s40Goal)
def s40Witnesses := unpackWitnesses s40StockWords [1538, 265218, 607362, 820226, 1131554]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 4 := by
  apply essentialLower (witnesses := s40Witnesses)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
-- s41: K3C5 (lb=9, vars=6, kind=2)
def s41Mask : Word := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
abbrev s41Goal : Word := sGoal &&& s41Mask
abbrev s41StockWords : List Word := projectDAGStock s41Mask sBase [0, 1, 2, 5, 6, 7]
def s41Fact : Bound := (s41Mask, s41StockWords, 9, s41Goal)
def s41Witnesses := unpackWitnesses s41StockWords [1538, 263681, 526849, 803329, 1082370, 1392672]
def s41Cuts : List Bound := [s8Fact, s29Fact, s32Fact, s33Fact, s34Fact, s3Fact, s35Fact, s36Fact, s37Fact, s38Fact, s39Fact, s40Fact]
def s41Chart : Option RowChart := some ⟨[3, 5, 6, 33, 66, 160, 192, 7, 35, 37, 38, 67, 100, 34, 36, 65, 68, 96, 129, 130, 132, 1, 2, 4], rfl⟩
def s41Sample : DagSample := (0x486512198886522198c06530198c8a432310c8e03239102034100d04064110844422080d08a042300440311188c8263211504a242015080611084442611288826140815022140b0444232090c824532094c84632184c86232198c8651101882052088482c1, 45)
def s41Links : DagLinks :=
  dagLookupLinks 0x8888888888887a786a685350420f01 0xd620498a37d110628c040581a280a13e8883143fa218c54a62840131807880242010003f 8 3 12 4 1 6
def s41Data : Forest := fun i => decodeNode 4 16 0xf446040403440284f4423142f44131513141013100f10091008103f0 i
def s41Tags := dagTraceTags s41Mask 45 (dagTagBases s41StockWords 0xf030844003fb8ca812df1fec09a7a9797fa406d21cf150fceac32d150624a9fe97 0xf30e1c0007f821810ff7cfc23c709fc79e066c00fc00078c9c20100042001ec07 45) 8 s41Data
def s41States := dagTrace s41Mask s41StockWords 8 s41Data
def s41MoveCert : List (DagMoveRecord 256) := []
def s41Moves := dagMoves s41MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Autos : DagMovesOK s41Mask s41Goal 256 s41Moves := dagMovesOfCheck (by decide +kernel)
def s41Check := dagCheckNode s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) 14 s41States s41Moves s41Links s41Sample s41Tags
def s41RootAt (token : Nat) : Bool :=
  let s := rootState s41StockWords 8 token
  !dagAllowedRoot s41Witnesses s.2.1 || dagLocal s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s ||
  dagRef 14 s41States s41Moves s41Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41RootBlock0 : treeBlock 0 64 s41RootAt = true := by decide +kernel
theorem s41RootVerified : treeBlock 0 64 s41RootAt = true := s41RootBlock0
theorem s41Roots : dagCheckRoots s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s41Witnesses (dagRef 14 s41States s41Moves s41Links 0) s41StockWords 8 = true := s41RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block0 : treeBlock 0 14 s41Check = true := by decide +kernel
theorem s41Verified : treeBlock 0 14 s41Check = true := s41Block0
theorem s41Blocks : treeBlock 0 14 s41Check = true := s41Verified
theorem s41Known : Known s41Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s40Stock) s39Stock) s38Stock) s37Stock) s36Stock) s35Stock) s3Stock) s34Stock) s33Stock) s32Stock) s29Stock) s8Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 9 := by
  apply lowerDag _ _ _ _ s41Autos _ _ _ s41Known _ s41Roots s41Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s41StockWords; decide +kernel
  · decide +kernel
  · simp only [s41Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
-- s44: 20_10_60_70 (lb=5, vars=4, kind=1)
def s44Mask : Word := 0x303030303030303
abbrev s44Goal : Word := sGoal &&& s44Mask
abbrev s44StockWords : List Word := projectDAGStock s44Mask sBase [0, 3, 4, 5]
def s44Fact : Bound := (s44Mask, s44StockWords, 5, s44Goal)
def s44Witnesses := unpackWitnesses s44StockWords [4616, 266753, 532993, 803329]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 5 := by
  apply essentialLift (witnesses := s44Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
-- s45: 20_10_60_71 (lb=5, vars=4, kind=1)
def s45Mask : Word := 0x30303030303030300000000000000000000000000000000
abbrev s45Goal : Word := sGoal &&& s45Mask
abbrev s45StockWords : List Word := projectDAGStock s45Mask sBase [0, 3, 4, 5]
def s45Fact : Bound := (s45Mask, s45StockWords, 5, s45Goal)
def s45Witnesses := unpackWitnesses s45StockWords [70280, 332417, 598657, 868480]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 5 := by
  apply essentialLift (witnesses := s45Witnesses) (cut := s20Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s20StockWords) (by decide +kernel)
  · exact s20Stock
  · decide +kernel
-- s46: 20_10_60 (lb=7, vars=5, kind=2)
def s46Mask : Word := 0x30303030303030300000000000000000303030303030303
abbrev s46Goal : Word := sGoal &&& s46Mask
abbrev s46StockWords : List Word := projectDAGStock s46Mask sBase [0, 3, 4, 5, 7]
def s46Fact : Bound := (s46Mask, s46StockWords, 7, s46Goal)
def s46Witnesses := unpackWitnesses s46StockWords [4616, 266753, 532993, 803329, 1130528]
def s46Cuts : List Bound := [s44Fact, s45Fact]
def s46Chart : Option RowChart := some ⟨[9, 17, 24, 33, 160, 25, 41, 49, 56, 137, 145, 152, 40, 48, 129, 136, 144, 1, 8, 16, 32, 128, 0, 40], rfl⟩
def s46Sample : DagSample := (0x40211402450211804520984828120b01406060181808510984824510a8140a46031180e11089140e102a140a450289, 21)
def s46Links : DagLinks :=
  dagLookupLinks 0x28a28301 0x392c662023141008001f 6 3 12 2 2 5
def s46Data : Forest := fun i => decodeNode 3 15 0x92c2628402080f8 i
def s46Tags := dagTraceTags s46Mask 21 (dagTagBases s46StockWords 0x1c717a64f60dd9a926b73e0ad7 0x1c717f1c740f698184b3000007 21) 6 s46Data
def s46States := dagTrace s46Mask s46StockWords 6 s46Data
def s46Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s46MoveCert : List (DagMoveRecord 256) := [([([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])], s46Move0Map, s46Move0Map)]
def s46Moves := dagMoves s46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Autos : DagMovesOK s46Mask s46Goal 256 s46Moves := dagMovesOfCheck (by decide +kernel)
def s46Check := dagCheckNode s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) 4 s46States s46Moves s46Links s46Sample s46Tags
def s46RootAt (token : Nat) : Bool :=
  let s := rootState s46StockWords 6 token
  !dagAllowedRoot s46Witnesses s.2.1 || dagLocal s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s ||
  dagRef 4 s46States s46Moves s46Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46RootBlock0 : treeBlock 0 32 s46RootAt = true := by decide +kernel
theorem s46RootVerified : treeBlock 0 32 s46RootAt = true := s46RootBlock0
theorem s46Roots : dagCheckRoots s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s46Witnesses (dagRef 4 s46States s46Moves s46Links 0) s46StockWords 6 = true := s46RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block0 : treeBlock 0 4 s46Check = true := by decide +kernel
theorem s46Verified : treeBlock 0 4 s46Check = true := s46Block0
theorem s46Blocks : treeBlock 0 4 s46Check = true := s46Verified
theorem s46Known : Known s46Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s45Stock) s44Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 7 := by
  apply lowerDag _ _ _ _ s46Autos _ _ _ s46Known _ s46Roots s46Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s46StockWords; decide +kernel
  · decide +kernel
  · simp only [s46Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
-- s47: 20_10 (lb=8, vars=6, kind=1)
def s47Mask : Word := 0x303030303030303030303030303030303030303030303030303030303030303
abbrev s47Goal : Word := sGoal &&& s47Mask
abbrev s47StockWords : List Word := projectDAGStock s47Mask sBase [0, 3, 4, 5, 6, 7]
def s47Fact : Bound := (s47Mask, s47StockWords, 8, s47Goal)
def s47Witnesses := unpackWitnesses s47StockWords [4616, 266753, 532993, 803329, 1147008, 1392672]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 8 := by
  apply essentialLift (witnesses := s47Witnesses) (cut := s46Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s46StockWords) (by decide +kernel)
  · exact s46Stock
  · decide +kernel
-- s56: 20_31 (lb=6, vars=6, kind=1)
def s56Mask : Word := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
abbrev s56Goal : Word := sGoal &&& s56Mask
abbrev s56StockWords : List Word := projectDAGStock s56Mask sBase [0, 1, 4, 5, 6, 7]
def s56Fact : Bound := (s56Mask, s56StockWords, 6, s56Goal)
def s56Witnesses := unpackWitnesses s56StockWords [4616, 300104, 536584, 872584, 1086474, 1396776]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 6 := by
  apply essentialLift (witnesses := s56Witnesses) (cut := s22Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s22StockWords) (by decide +kernel)
  · exact s22Stock
  · decide +kernel
-- s64: 30_50 (lb=8, vars=6, kind=1)
def s64Mask : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev s64Goal : Word := sGoal &&& s64Mask
abbrev s64StockWords : List Word := projectDAGStock s64Mask sBase [0, 1, 2, 4, 6, 7]
def s64Fact : Bound := (s64Mask, s64StockWords, 8, s64Goal)
def s64Witnesses := unpackWitnesses s64StockWords [1538, 263681, 526849, 795137, 1082370, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 8 := by
  apply essentialLift (witnesses := s64Witnesses) (cut := s29Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s29StockWords) (by decide +kernel)
  · exact s29Stock
  · decide +kernel
-- s72: 50_10_61 (lb=6, vars=5, kind=1)
def s72Mask : Word := 0x33333333000000000000000000000000333333330000000000000000
abbrev s72Goal : Word := sGoal &&& s72Mask
abbrev s72StockWords : List Word := projectDAGStock s72Mask sBase [0, 2, 3, 4, 7]
def s72Fact : Bound := (s72Mask, s72StockWords, 6, s72Goal)
def s72Witnesses := unpackWitnesses s72StockWords [35396, 297537, 561729, 827969, 1146944]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 6 := by
  apply essentialLift (witnesses := s72Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
-- s87: 50_70 (lb=9, vars=6, kind=1)
def s87Mask : Word := 0xffffffff00000000ffffffff
abbrev s87Goal : Word := sGoal &&& s87Mask
abbrev s87StockWords : List Word := projectDAGStock s87Mask sBase [0, 1, 2, 3, 4, 6]
def s87Fact : Bound := (s87Mask, s87StockWords, 9, s87Goal)
def s87Witnesses := unpackWitnesses s87StockWords [1538, 263681, 526849, 791041, 1057281, 1344514]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 9 := by
  apply essentialLift (witnesses := s87Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel

def targetWord : Word := 0xffffffffffeeffecffffffffffeaffe8ffffffffffeeeeecffeeeeecffeaeae8
def axisMap (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 3, 4, 7] 0 i.val)
def graphMoves : List (DagMoveRecord 256) := [([([(0x9999999999999999999999999999999999999999999999999999999999999999,0),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0x4444444444444444444444444444444444444444444444444444444444444444,1)]),([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff,0),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,24)]),([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff,0),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,48)])],axisMap,axisMap)]
structure FiniteCase where
  mask : Word
  axes : List Nat
  fuel : Nat
  count : Nat
  witnessCodes : List Nat
  chart : RowChart
  sample : DagSample
  positiveTags : Nat
  negativeTags : Nat
  forest : Forest
  moves : List (DagMoveRecord 256)
  links : DagLinks

def caseStock (c : FiniteCase) := projectDAGStock c.mask sBase c.axes
def caseGoal (c : FiniteCase) := targetWord &&& c.mask
def caseBound (c : FiniteCase) : Bound := (c.mask,caseStock c,c.fuel+1,caseGoal c)
def caseStates (c : FiniteCase) := dagTrace c.mask (caseStock c) c.fuel c.forest
def caseTags (c : FiniteCase) := dagTraceTags c.mask c.sample.2
  (dagTagBases (caseStock c) c.positiveTags c.negativeTags c.sample.2) c.fuel c.forest
def caseWitnesses (c : FiniteCase) := unpackWitnesses (caseStock c) c.witnessCodes
def caseNode (c : FiniteCase) (previous : List Bound) :=
  dagCheckNode c.mask (caseGoal c) (some c.chart) (dagKnownCloses (caseGoal c) previous)
    c.count (caseStates c) (dagMoves c.moves) c.links c.sample (caseTags c)
def caseRoots (c : FiniteCase) (previous : List Bound) :=
  dagCheckRoots c.mask (caseGoal c) (some c.chart) (dagKnownCloses (caseGoal c) previous)
    (caseWitnesses c) (dagRef c.count (caseStates c) (dagMoves c.moves) c.links 0) (caseStock c) c.fuel

def CaseConditions (c : FiniteCase) (previous : List Bound) : Prop :=
  Masked (fullMask 256) c.mask ∧ Masked c.mask (caseGoal c) ∧
  properWord c.mask (caseGoal c) ∧ chartCheck (caseGoal c) (some c.chart)=true ∧
  c.moves.all (dagMoveRecordOK c.mask (caseGoal c))=true ∧
  (caseStock c).all (fun w => w &&& c.mask == w)=true ∧ (caseStock c).Nodup ∧
  (caseWitnesses c).all (essentialB c.mask (caseGoal c) (caseStock c))=true ∧
  previous.all (fun b => c.mask &&& b.1 == b.1)=true

instance caseConditionsDecidable (c : FiniteCase) (previous : List Bound) : Decidable (CaseConditions c previous) := by
  unfold CaseConditions Masked properWord
  infer_instance

theorem caseSound (c : FiniteCase) (previous : List Bound) (known : Known previous)
    (checks : CaseConditions c previous) (roots : caseRoots c previous=true)
    (nodes : treeBlock 0 c.count (caseNode c previous)=true) :
    Lower c.mask (caseStock c) (caseGoal c) (c.fuel+1) := by
  obtain ⟨maskOK,goalOK,proper,chart,moves,stock,nodup,essential,sub⟩ := checks
  exact lowerDag (width:=256) (count:=c.count) (forest:=c.forest)
    (chart:=some c.chart) (moves:=dagMoves c.moves) (links:=c.links)
    (sample:=c.sample) (tags:=caseTags c) (bounds:=previous)
    (witnesses:=caseWitnesses c)
    maskOK goalOK proper (chartOfCheck chart) (dagMovesOfCheck moves)
    (stockMaskedOfCheck stock) nodup essential known
    (fun b hb => beq_iff_eq.mp (List.all_eq_true.mp sub b hb)) roots nodes

def projectFact (m : Word) (axes : List Nat) (n : Nat) : Bound := (m,projectDAGStock m sBase axes,n,targetWord &&& m)
abbrev Holds (b : Bound) := Lower b.1 b.2.1 b.2.2.2 b.2.2.1
def vf1 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333,2)],[(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,2)])
def vf4 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,16)],[(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,16)])
def vf5 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff,32)],[(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,32)])
def vf6 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff,64)],[(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,64)])
def vf7 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff,128)],[(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,128)])
def vs01 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999,0),(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0x4444444444444444444444444444444444444444444444444444444444444444,1)])
def vs02 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0x5050505050505050505050505050505050505050505050505050505050505050,3)])
def vs03 : WordMoveStep := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55,0),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0x5500550055005500550055005500550055005500550055005500550055005500,7)])
def vs05 : WordMoveStep := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555,0),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0x5555555500000000555555550000000055555555000000005555555500000000,31)])
def vs06 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555,0),(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,63)],[(0x5555555555555555000000000000000055555555555555550000000000000000,63)])
def vs07 : WordMoveStep := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555,0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,127)],[(0x5555555555555555555555555555555500000000000000000000000000000000,127)])
def vs12 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0x3030303030303030303030303030303030303030303030303030303030303030,2)])
def vs13 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33,0),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0x3300330033003300330033003300330033003300330033003300330033003300,6)])
def vs14 : WordMoveStep := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333,0),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0x3333000033330000333300003333000033330000333300003333000033330000,14)])
def vs15 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333,0),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0x3333333300000000333333330000000033333333000000003333333300000000,30)])
def vs16 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333,0),(0xcccccccccccccccc0000000000000000cccccccccccccccc,62)],[(0x3333333333333333000000000000000033333333333333330000000000000000,62)])
def vs17 : WordMoveStep := ([(0xcccccccccccccccccccccccccccccccc33333333333333333333333333333333,0),(0xcccccccccccccccccccccccccccccccc,126)],[(0x3333333333333333333333333333333300000000000000000000000000000000,126)])
def vs23 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f,0),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00,4)])
def vs24 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f,0),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,12)])
def vs25 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f,0),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)],[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000,28)])
def vs26 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f,0),(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,60)],[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,60)])
def vs27 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,124)],[(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000,124)])
def vs34 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff,0),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000,8)])
def vs35 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff,0),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000,24)])
def vs36 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff,0),(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00,56)],[(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000,56)])
def vs37 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff,0),(0xff00ff00ff00ff00ff00ff00ff00ff00,120)],[(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,120)])
def vs45 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff,0),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xffff000000000000ffff000000000000ffff000000000000ffff00000000,16)])
def vs46 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff,0),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)],[(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,48)])
def vs47 : WordMoveStep := ([(0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff,0),(0xffff0000ffff0000ffff0000ffff0000,112)],[(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,112)])
def vs56 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff,0),(0xffffffff000000000000000000000000ffffffff00000000,32)],[(0xffffffff000000000000000000000000ffffffff0000000000000000,32)])
def vs57 : WordMoveStep := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff,0),(0xffffffff00000000ffffffff00000000,96)],[(0xffffffff00000000ffffffff00000000000000000000000000000000,96)])
def vs67 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff,0),(0xffffffffffffffff0000000000000000,64)],[(0xffffffffffffffff00000000000000000000000000000000,64)])
def r0 : Bound := projectFact 0x55005500550055005500550055005500 [1, 2, 4, 5, 6] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0p : Holds r0 := dagShiftLower (width:=256) [vs01,vs35,vs47,vs46,vf5,vf6] s72Stock (by decide +kernel)
def r1 : Bound := projectFact 0xff000000ff000000ff000000ff [0, 1, 2, 5, 6] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1p : Holds r1 := dagShiftLower (width:=256) [vs01,vs35,vs46] s18Stock (by decide +kernel)
def r2 : Bound := projectFact 0x50500000505000005050000050500000505000005050000050500000505 [1, 3, 5, 6, 7] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2p : Holds r2 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs17,vs25,vs12,vs26] s29Stock (by decide +kernel)
def r3 : Bound := projectFact 0xffff0000000000000000000000000000ffff [0, 1, 2, 3, 7] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3p : Holds r3 := dagShiftLower (width:=256) [vs01,vs36,vs34,vs45] s29Stock (by decide +kernel)
def r4 : Bound := projectFact 0x50000000500000005000000050000000500000005000000050000000500 [1, 5, 6, 7] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r4p : Holds r4 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs15,vs27,vs26,vf5,vf7] s28Stock (by decide +kernel)
def r5 : Bound := projectFact 0xffff00000000000000000000000000000000 [0, 1, 2, 3] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r5p : Holds r5 := dagShiftLower (width:=256) [vs36,vs34,vs45] s28Stock (by decide +kernel)
def r7 : Bound := projectFact 0xffff0000ffff00000000000000000000ffff0000ffff [0, 1, 2, 3, 5, 7] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r7p : Holds r7 := dagShiftLower (width:=256) [vs35,vs34,vs46] s41Stock (by decide +kernel)
def r8 : Bound := projectFact 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f [0, 1, 3, 5, 6, 7] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r8p : Holds r8 := dagShiftLower (width:=256) [vs05,vs01,vs23,vs27,vs26] s41Stock (by decide +kernel)
def r9 : Bound := projectFact 0xf0f00000f0f000000000000000000000f0f00000f0f [0, 1, 3, 5, 7] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r9p : Holds r9 := dagShiftLower (width:=256) [vs35,vs34,vs46] s8Stock (by decide +kernel)
def r10 : Bound := projectFact 0x500000005000000050000000500000005000000050000000500000005 [1, 5, 6, 7] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r10p : Holds r10 := dagShiftLower (width:=256) [vs03,vs25,vs06,vs47,vs02] s9Stock (by decide +kernel)
def r11 : Bound := projectFact 0xffff [0, 1, 2, 3] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r11p : Holds r11 := dagShiftLower (width:=256) [vs34] s9Stock (by decide +kernel)
def r12 : Bound := projectFact 0x5500000055000000550000005500 [1, 2, 5, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r12p : Holds r12 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs15,vs26,vf5] s9Stock (by decide +kernel)
def r13 : Bound := projectFact 0xff00000000000000ff00000000000000000000000000000000 [0, 1, 2, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r13p : Holds r13 := dagShiftLower (width:=256) [vs01,vs45,vs46,vf7] s9Stock (by decide +kernel)
def r14 : Bound := projectFact 0xf0f00000f0f00000f0f00000f0f [0, 1, 3, 5, 6] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r14p : Holds r14 := dagShiftLower (width:=256) [vs06,vs23,vs27,vs05,vs25] s29Stock (by decide +kernel)
def r15 : Bound := projectFact 0xff000000ff0000000000000000000000ff000000ff [0, 1, 2, 5, 7] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r15p : Holds r15 := dagShiftLower (width:=256) [vs56] s29Stock (by decide +kernel)
def r16 : Bound := projectFact 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 [0, 1, 2, 3, 5, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16p : Holds r16 := dagShiftLower (width:=256) [vs06,vs01,vs12,vs37,vs24,vs45,vs35] s56Stock (by decide +kernel)
def r17 : Bound := projectFact 0xf0000000f0000000f0000000f00 [0, 1, 5, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r17p : Holds r17 := dagShiftLower (width:=256) [vs06,vs01,vs23,vs24,vs25,vs12,vf4,vf7] s28Stock (by decide +kernel)
def r18 : Bound := projectFact 0xff000000ff00000000000000000000000000000000 [0, 1, 2, 5] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r18p : Holds r18 := dagShiftLower (width:=256) [vs56] s28Stock (by decide +kernel)
def r19 : Bound := projectFact 0x10100000101000001010000010100000101000001010000010100000101 [3, 5, 6, 7] 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r19p : Holds r19 := dagShiftLower (width:=256) [vs12,vs13,vs57,vs56] s2Stock (by decide +kernel)
def r21 : Bound := projectFact 0x5000500050005000500050005000500 [1, 4, 5, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r21p : Holds r21 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs15,vs26,vf5,vf7] s28Stock (by decide +kernel)
def r22 : Bound := projectFact 0xf0000000f0000000f0000000f0000 [0, 1, 5, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r22p : Holds r22 := dagShiftLower (width:=256) [vs06,vs01,vs23,vs24,vs25,vs12,vf5,vf7] s28Stock (by decide +kernel)
def r23 : Bound := projectFact 0xf0f0f0f0f0f0f0f [0, 1, 3, 4, 5] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r23p : Holds r23 := dagShiftLower (width:=256) [vs01,vs06,vs23,vs02,vs24,vs57] s29Stock (by decide +kernel)
def r24 : Bound := projectFact 0x3030303000000000303030300000000 [0, 3, 4, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r24p : Holds r24 := dagShiftLower (width:=256) [vs13,vs24,vf5,vf7] s28Stock (by decide +kernel)
def r25 : Bound := projectFact 0xf0f0f0f000000000f0f0f0f [0, 1, 3, 4, 6] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r25p : Holds r25 := dagShiftLower (width:=256) [vs01,vs06,vs23,vs02,vs24,vs45,vs57] s29Stock (by decide +kernel)
def r26 : Bound := projectFact 0x3030303030303030000000000000000 [0, 3, 4, 5] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r26p : Holds r26 := dagShiftLower (width:=256) [vs13,vs24,vs56,vf5,vf7] s28Stock (by decide +kernel)
def r27 : Bound := projectFact 0x5050000050500000505000005050000 [1, 3, 5, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r27p : Holds r27 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs16,vs25,vs12,vf5,vf7] s28Stock (by decide +kernel)
def r28 : Bound := projectFact 0xf000f000f000f000f000f000f000f [0, 1, 4, 5, 6] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r28p : Holds r28 := dagShiftLower (width:=256) [vs06,vs23,vs24,vs27,vs05,vs25] s29Stock (by decide +kernel)
def r29 : Bound := projectFact 0xf0f0f0f0000000000000000 [0, 1, 3, 4] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r29p : Holds r29 := dagShiftLower (width:=256) [vs16,vs23,vs12,vs24,vs45,vf5,vf7] s28Stock (by decide +kernel)
def r30 : Bound := projectFact 0xf0f0f0f00000000 [0, 1, 3, 4] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r30p : Holds r30 := dagShiftLower (width:=256) [vs16,vs23,vs12,vs24,vs45,vf4,vf7] s28Stock (by decide +kernel)
def r32 : Bound := projectFact 0x3030303000000000000000000000000030303030000000000000000 [0, 3, 4, 7] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r32p : Holds r32 := dagShiftLower (width:=256) [vs01,vs03,vs25,vs24,vs46,vs47,vf7] s9Stock (by decide +kernel)
def r33 : Bound := projectFact 0x5000000050000000500000005000000050000000500000005000000050000 [1, 5, 6, 7] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r33p : Holds r33 := dagShiftLower (width:=256) [vs03,vs25,vs06,vs47,vs02,vf7] s9Stock (by decide +kernel)
def r34 : Bound := projectFact 0x30303030303030300000000000000000303030303030303 [0, 3, 4, 5, 7] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r34p : Holds r34 := dagShiftLower (width:=256) [vs13,vs24,vs57,vs56] s29Stock (by decide +kernel)
def r35 : Bound := projectFact 0x30303030000000000000000000000000303030300000000 [0, 3, 4, 7] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r35p : Holds r35 := dagShiftLower (width:=256) [vs13,vs24,vs67,vf5,vf7] s28Stock (by decide +kernel)
def r36 : Bound := projectFact 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f [0, 1, 3, 4, 5, 7] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r36p : Holds r36 := dagShiftLower (width:=256) [vs15,vs23,vs12,vs24,vs47,vs46] s41Stock (by decide +kernel)
def r37 : Bound := projectFact 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f [0, 1, 5, 6, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r37p : Holds r37 := dagShiftLower (width:=256) [vs05,vs01,vs23,vs24,vs27,vs26] s33Stock (by decide +kernel)
def r38 : Bound := projectFact 0xf0f0f0f0000000000000000000000000f0f0f0f [0, 1, 3, 4, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r38p : Holds r38 := dagShiftLower (width:=256) [vs15,vs23,vs12,vs24,vs67] s33Stock (by decide +kernel)
def r41 : Bound := projectFact 0xffffffff00000000ffffffff [0, 1, 2, 3, 4, 6] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r41p : Holds r41 := dagShiftLower (width:=256) [] s87Stock (by decide +kernel)
def r42 : Bound := projectFact 0xff00ff00ff00ff00ff00ff00ff00ff [0, 1, 2, 4, 5, 6] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r42p : Holds r42 := dagShiftLower (width:=256) [vs01,vs35,vs46] s87Stock (by decide +kernel)
def r43 : Bound := projectFact 0x33333333000000003333333300000000 [0, 2, 3, 4, 6] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r43p : Holds r43 := dagShiftLower (width:=256) [vs67,vf5,vf6] s72Stock (by decide +kernel)
def r44 : Bound := projectFact 0x505050505050505050505050505050505050505050505050505050505050505 [1, 3, 4, 5, 6, 7] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r44p : Holds r44 := dagShiftLower (width:=256) [vs01,vs03,vs07,vs46,vs05] s47Stock (by decide +kernel)
def r45 : Bound := projectFact 0xffffffff [0, 1, 2, 3, 4] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r45p : Holds r45 := dagShiftLower (width:=256) [] s18Stock (by decide +kernel)
def r46 : Bound := projectFact 0x55000000550000005500000055 [1, 2, 5, 6] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r46p : Holds r46 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs15,vs26] s9Stock (by decide +kernel)
def r47 : Bound := projectFact 0xff000000ff000000ff000000ff0000 [0, 1, 2, 5, 6] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r47p : Holds r47 := dagShiftLower (width:=256) [vs07,vs01,vs13,vs45,vs34,vs46,vf5,vf6] s72Stock (by decide +kernel)
def r48 : Bound := projectFact 0xff000000ff000000ff000000ff00 [0, 1, 2, 5, 6] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r48p : Holds r48 := dagShiftLower (width:=256) [vs07,vs01,vs13,vs45,vs34,vs46,vf1,vf6] s72Stock (by decide +kernel)
def r49 : Bound := projectFact 0x33333333 [0, 2, 3, 4] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r49p : Holds r49 := dagShiftLower (width:=256) [vs13,vs24] s9Stock (by decide +kernel)
def r50 : Bound := projectFact 0xff00ff0000000000ff00ff [0, 1, 2, 4, 6] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r50p : Holds r50 := dagShiftLower (width:=256) [vs45] s33Stock (by decide +kernel)
def r51 : Bound := projectFact 0xff00ff00ff00ff [0, 1, 2, 4, 5] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r51p : Holds r51 := dagShiftLower (width:=256) [vs45,vs46] s33Stock (by decide +kernel)
def r52 : Bound := projectFact 0xffff0000ffff [0, 1, 2, 3, 5] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r52p : Holds r52 := dagShiftLower (width:=256) [vs35,vs34,vs46] s33Stock (by decide +kernel)
def r54 : Bound := projectFact 0x333333333333333300000000000000003333333333333333 [0, 2, 3, 4, 5, 7] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r54p : Holds r54 := dagShiftLower (width:=256) [vs13,vs24,vs57,vs56] s64Stock (by decide +kernel)
def r55 : Bound := projectFact 0x55000000550000005500000055000000550000005500000055000000550000 [1, 2, 5, 6, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r55p : Holds r55 := dagShiftLower (width:=256) [vs03,vs01,vs25,vs14,vs17,vs12,vs26,vf7] s33Stock (by decide +kernel)
def r56 : Bound := projectFact 0x33333333000000000000000000000000333333330000000000000000 [0, 2, 3, 4, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r56p : Holds r56 := dagShiftLower (width:=256) [vs13,vs25,vs24,vs67,vf7] s33Stock (by decide +kernel)
def r57 : Bound := projectFact 0xff00ff0000000000ff00ff00000000000000000000000000000000 [0, 1, 2, 4, 6] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r57p : Holds r57 := dagShiftLower (width:=256) [vs45,vf7] s33Stock (by decide +kernel)
def r58 : Bound := projectFact 0x555500005555000055550000555500005555000055550000555500005555 [1, 2, 3, 5, 6, 7] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r58p : Holds r58 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs17,vs25,vs12,vs26] s64Stock (by decide +kernel)
def r59 : Bound := projectFact 0x303030303030303030303030303030303030303030303030303030303030303 [0, 3, 4, 5, 6, 7] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r59p : Holds r59 := dagShiftLower (width:=256) [vs03,vs57] s47Stock (by decide +kernel)
def r60 : Bound := projectFact 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff [0, 1, 2, 5, 6, 7] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r60p : Holds r60 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs15,vs27,vs26] s87Stock (by decide +kernel)
def r61 : Bound := projectFact 0xffffffff000000000000000000000000ffffffff [0, 1, 2, 3, 4, 7] 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r61p : Holds r61 := dagShiftLower (width:=256) [vs13,vs24,vs67] s87Stock (by decide +kernel)
def r62 : Bound := projectFact 0x550000005500000055000000550000005500000055000000550000005500 [1, 2, 5, 6, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r62p : Holds r62 := dagShiftLower (width:=256) [vs01,vs35,vs46,vf5,vf6] s72Stock (by decide +kernel)
def r63 : Bound := projectFact 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f [0, 1, 3, 4, 6, 7] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r63p : Holds r63 := dagShiftLower (width:=256) [vs01,vs06,vs23,vs02,vs24,vs47] s64Stock (by decide +kernel)
def r64 : Bound := projectFact 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff [0, 1, 2, 4, 5, 7] 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r64p : Holds r64 := dagShiftLower (width:=256) [vs56] s64Stock (by decide +kernel)
def r65 : Bound := projectFact 0x303030300000000030303030000000003030303000000000303030300000000 [0, 3, 4, 6, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r65p : Holds r65 := dagShiftLower (width:=256) [vs13,vs24,vs57,vs56] s34Stock (by decide +kernel)
def r66 : Bound := projectFact 0x500050005000500050005000500050005000500050005000500050005000500 [1, 4, 5, 6, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r66p : Holds r66 := dagShiftLower (width:=256) [vs03,vs01,vs24,vs17,vs25,vs12,vs26] s34Stock (by decide +kernel)
def r67 : Bound := projectFact 0x505000005050000050500000505000005050000050500000505000005050000 [1, 3, 5, 6, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r67p : Holds r67 := dagShiftLower (width:=256) [vs01,vs03,vs25,vs07,vs46,vs02] s72Stock (by decide +kernel)
def r68 : Bound := projectFact 0x333333330000000000000000000000003333333300000000 [0, 2, 3, 4, 7] 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r68p : Holds r68 := dagShiftLower (width:=256) [vf5,vf6] s72Stock (by decide +kernel)
def r69 : Bound := projectFact 0x303030300000000000000000000000003030303 [0, 3, 4, 7] 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r69p : Holds r69 := dagShiftLower (width:=256) [vs01,vs03,vs25,vs24,vs46,vs47] s9Stock (by decide +kernel)
def c0 : FiniteCase := ⟨0x555555555555555500000000000000005555555555555555,[1, 2, 3, 4, 5, 7],6,1,[3076, 265218, 536592, 798728, 1065986, 1380360],⟨[6, 24, 34, 136, 160, 190, 30, 46, 54, 58, 60, 142, 10, 44, 52, 146, 148, 0, 2, 4, 8, 12, 16, 18],rfl⟩,(0x4a2d1289c4a25924b2492692496482c1209842291088c4221904a24122904864028100881a2d0683c1a0d860b0180e06032162b0583c160b850a8140e0502a1229048261028040220a0702816090c8241a09058201806230181c06038148a050a8141a050381088040600806010880406,50),0xffff924a024424a4bfffc8082ff00fd20fd12125252fc25ff8e4e4e38ccb894f0f09255e3e7,0xffff0000000000003fffc0000ff00fc00fc00000000fc00ff8e0e0e38cc381070700000e1e3,(decodeNode 1 7 0x7e),[],(dagLookupLinks 0x9 0x3f 2 1 6 1 1 2)⟩
def c0Bounds : List Bound := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0Proof : Holds (caseBound c0) := caseSound c0 c0Bounds (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def r6 : Bound := projectFact 0x333300003333000033330000333300003333000033330000333300003333 [0, 2, 3, 5, 6, 7] 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r6p : Holds r6 := dagShiftLower (width:=256) [vs01,vs35,vs46] c0Proof (by decide +kernel)
def c1 : FiniteCase := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,[0, 1, 2, 3, 5, 6, 7],11,2129,[1538, 263681, 526849, 791041, 1065986, 1344514, 1642504],⟨[3, 5, 6, 9, 34, 66, 96, 136, 160, 239, 15, 39, 10, 33, 44, 76, 130, 193, 196, 0, 1, 2, 4, 8],rfl⟩,(0x26180420d0118104a44101850606201442e0602201449050a4040562180588c422809864261a1804260a0c906026038904214088580e623088842160a802830010800220082c00066211588856098502a02402498451402458252082442094081482052218108884122104032098102884201888061201982c22090842224110904224080d04a00108c00032422050886028014420508818881218042050501814882080c420306018482210a8042601201414030602414096239188cc6231988c560b8582c960b1582c36038180c86030908a44223108864221504c241289048a41219048340a85028940a15028340281008826330986c26138984d2432090682412890492219088462211482612092482452090c80602010858ac161b0582e160b450a8141a0502a140a448a41219048261209442a110984422910894422310280406010088188c06038180d05228144a050a8140e0502c10880402408060201404420108804060100c0209008140203,164),0x118620905006441391083ffffff88004444248400a549d4c8a408868048043ff8400ffffa222104040b52b922431088158a81c222422244917ffff8202040e489220ac640031100d112111ff087f8107fe045a150901c530380006223c87888f0e4787887119208006fff00013fec62f108497c4224291104af97942702012eff1002c04c3c7c087c113e088fc10a8f,0x1a8a6080f02764f080003ffffff000000000000008289fcc0ec98960280803ff8000ffff800000000045040320034009010c5e000000000007ffff8000084659f200f0000037321c000000ff007f8007fe00820f89e0c50c38001832bc07800f0e0787807018038700000000300d8630140007c00000000000f8784100201230f0c72004cc03c003c001e0007c00007,(decodeNode 12 25 0x12507287a23940131c724a0df0f446f861c37c24b1be1e88deec386f792837abd11bd5870dea92c6f518a37a8d31b80020dc12506cc7a2361bd31afe4a0d3325068f0243430131a0c698cfe3586751a633a81219c8098cdd25066361c331a4b198d280cc4c406601a0330250197c038cb1250651496328c941935258c9b25064c61c32624b1930c40c9925063f49631fc9418f9870c7c92c63e31031f01318f0068c79250633496319c9418bd258c5e62062f92831730e18b9258c5c62062e18a31701218a4090c1004c6050082f28131770098bb00485c29282daa4b16d4c40b6b2505b44962da18816d24a0b6492c5b23102d949416c1258b606205b09282d724b16b8c40b5c3145ae0262b9c9415c00b0ade04c56f0262b701615a9e88ac72505469282a13d11509e88a7ec3853f01a28130f1398c409a52504d07a726830e13412589a06204d061c267c941335e9c99ac384cd496266988133466898a6344c17a624698811fe4a08faf4447d61c23ea4b11f4c408faf4447c61c23e49411e9e888f4c3847a49623d18811e86988f2c4847602c23aa5011b06b08d634c46b31a2348d0112408088a04c3e79281ef3d10f798707bc92c3de02a1ee80a0f6c0907ac0483d40261e880a0f440787992503ae7a21d730e0eb925875c6243a90121cc8ca0e4405070801c3841a01c08ca0df8c786e002836f0141b68070db46686d325035e7a21af30e0d792586bc62035e1a11af0cd8d780106bc01034f9281a3bd10d1d87068e92c34792819db160ce0c686712503367a219b3d10cd587066af48332928198bd10cc587066292c3319281983d10cc187066092c33018a1984940c8e4a063ef4431f7a218f30e0c7a4a0634f4431a61c18d24b0c6a4a0632f4431961c18ca4b0c64628633250313928187bd10c3de8861cc3830e9281853d10c2987061492c30a928183c940c0de88606f4430261c1814940bf9e885fcc382fe49617f4940bf5e885fac382fd49617e8c50bf40505dc0282e81ac16e8d00b746505ba3582d41a616a0ca0b524a055cf442a41ac1498d30a4e4a05192502887a21443d10a1d87050e04827402613825009a64a04c492c26231013149409852584c262026119a930c9409792584bc62025e19a92f1960924c9849263424931412480a090a4a047f25023b7a211dbd108e18704712502337a2119b0e08cd25846602822c18a112c94089125844862022419a9120c50890654430011218195109804484eab841a02a20d009106c94082aab841204220901b1048078826ab8410058208026104010882005441125020402c102494080469c40232a20100890080987f9e883fa0271fd00d8fed5707e1eb03ef55c1f67ad0fb30e07d2ab83e355c1ed9280f6bd687b6ab83d72501eb0270f580787ac0243d755c1e99280f2bd38795e883cac381e561c0f2557078deb43c6c381e33100f199307846c83c23581e119a0f08040786ab83c12501e07a20f030e07806b03c034e1e01a60f00cd07800223c00101e09280ed80f476d8703b52501d961c0ecc940761e883b12501d761c0ebb0e075926c3ac92c1d631b0eb4940755e9c3aaf441d561c0eaa5387552583aa6361d519e8eac940751e883a834e1d41a10ea5570748caa3a52501d1aae0e83d34741e883a06551d0aae0e7c96873deb439f55c1ce7ad0e7009873a4a039af4f1cd7a20e6809c7358703992501cb61c0e598f472de88394c431ca61c8e530e07280543920121c97ac0e1bd8070aab8382f4d1c17a20e0b13470587038204c1c0aae0dd81346ec08437602a1bb0090ddd5706e1e8837155c1b79280dbc9406d1882368c381b4aae0d8bd686c5e88362c381b14960d8bd506c1e9836064c1b03260d7d5706ba4b435d2501ae6208d730e06b925835c3581ab0320d5d5706a00943500481a8aae0d24940692ab83472541a202c0d155706864a034204e1a10268d0813068408234202a1a10090d0d57067deb433ec3819faae0cf3d506724a0334f4e19a7a48cd3d1066989c334c3819a7aa0cb8d2065aab832b2501957a70cabd1065589232ac381954960ca9968654c9c32a33e1953200ca557064e4a0326f5a1937a70c9bd2464de88326c4e19361c0c9a4b064d87032232919118a0c8b130642ab831f25018f61c0c7a50063cc4031e34118f1948c78c5063dea831d25418d1a60c6d57062587031355c1887a20c430e06212583106201879280c324b0618c5630c6201869280c2a4b0614c5630a62018519a8c2c94060d258306620183aae0c130e06092583046361821a08c1494060525830262b1813108c0988060466a30201f18100d8c0d57060187030092c1803100c00d046024a02fe92c17f3158bf98805fc6562fe31f17f18a8bf8c505fc06a2fe03c17c9280bd80f45ed8702f525017961c0bc98d05e24a02eef441770270bb81085dd8702ed25017561c0bab1205ce4a02e4f441723270b919085ca4a02e2f441711b20b70d605b86502dc01016eaae0b580c05a2ab82cf2501670188b3c940591e882c955c1609280b030e05812582c155c15e9280af3d38579e922bcf4415e61c0af24b05798982ba94015d9280adbd1056eab82b32501597a20acb0e056409c2b20421590148ac8048566ab82b0f5a15861c0ac24b0560c6c2b062a1583100ac557055e4a02aef4e1577a20abb0e055d2582ae64e1573188ab98a855cc402ae33e1573260aa99005506c82a63581531a00a98ca054c0202a755c14e0060a5d57052a4a029402514a0068a5494051de8828e048144aae0a14940509e88284c381427a68a03d1050189a280c381403268a01880502ab827d25a13e62089f30e04f925827c64113e31009f55704f24a0278f5a13c7a709e3d244f189c278c3813c49609e18d44f0c4027955c13b61c09da4b04eccb427665813b32609d98d84ecc6827662a13b31409d8c744ec6382772501397a209cb1384e588427294e1394a109c98a44e4c4027355c13792809bbd104dd87026e95a1374a709ba5084dd26c26e64e13732109b98804daab826af5a13561c09aa4b04d4c4026a336135aae09a49404d187026892c13431009a0d684d069c2692501327a209955704c64a0262f4413161c09898d84c6ab82612501307a209830e04c125826063613031509855704b40aa25b25012caae095bd344ade8825605512baae09549684a9eb425555c1297ad09480384a64a0250f4f1287a2094006c4a001e250c381279280933d38499e8824cc381264a709300f4499e8824ac4312561c892b0e0495e88248c38124aae091c96848deb4246c38123496091d57048a4a0244f5a1227a70913d1048987024492c12232d091193848807a2452501217a2090b138485884242c381214a10909938484c842420311219280903d3c481e88240c4f12062189030e448187024094312049b89024b0481e8823ec3811f31008fd570479eb423cc3811e49608f188047aab823b25011d61c08ea4b0474c4023b55c11c61c08e250447125823805a11c01b08e00a847003c23925011b7a208d988046eab823525011a7a208d30e0468c6c23555c11992808cbd1046587023292c119aae08c4940461e88230c3811802d08c01384600842300361187a208b990845c63a22e0341167ac088d57043de9a21ef4410f61c087c940439e8821c92c10e1a70870d0843865421c62010d31a8859960426ab8210f4d1087a208430e0420c9a21062010802a884557040c08420602a10300f081d570409e88204f58101aae07fc9403fdeb41fef440fd61c07ec9403ed8701f755c0f892d07c3d683e1e881f0c380f849607c3d503dcc981ee64c0f6aae07ac9683d64a01eaf5a0f561c07aa4b03d64c01e8f580f432c0790d903c86801e43340f219407955703c64b41e2f440f161c078a4b03c46b01e23420f11a00788cd03c46541e23280f1aae07849683c24a01e0f440f061c07824b03c0c401e033e0f00250783d503bc6981dec540ee4aa076a5303b4c981da64c0ec02a07655703ae4b41d72500eb7ad075b0e03ad2821d692c0eb32087598803ac0921d600d0eb7ac075557039eab81c72500e37ad071d5703864a01c204e0e10150708078386ab81bf2500db61c06dc940369e9c1b4f440da61c06d4998362ab81ab25b0d592806abd103558701aa92c0d532d06a9938354cb41a86400d4aae069c94034deb41a6f4e0d37a2069b0e034d2581a6f600d231a8693d50345e981a264c0cf1b20678d6033c66819e3280cfaae0674940339e8819cc380ce4960670d6033869c19c34c0ce19a0670ca833865019c33c0cdaae0664940331e92198f450cc7a2066313833187019892c0cc32d86618803306b619835a0cc1a70660cc833007c198c480cb4a40652500328c801946400c9024064d5703224a0190f5a0c87a70643d103218701909350c849606418d4320c4019003d0c8018864003432187018c3290c618a06300a431801018d55c0c49280623d683118701886410c431486218803106821883290c418f8620c503100821880290c400f8620020312ab8180c380c018a05f8c502faab817ac380bd31005e8c502f64a017203d0b961c05c49402dd87016f2500b67a205b49402cde8816664e0b3321059c9402c9e881643640af1ac0578ca02bc02015f2500ae7a20570d382b868415d2500ad7a205698d02ae4a0154f440aa62705531082a98701546290aa31005500c42aaab814b55c0a1928050c940281e8814155c09e92804f3d6827987013c92c09eaae04ec940275e9c13af4409d61c04ea4b02764a0138f4409c92804dbd1026cc9c13664209b4a604ca5002606c812e35809719a04b8ca025c02012f55c09692804b3d1025987012c92c09632704b1908258c5012b55c09492804a3d1025187012895a0944a704a250825126c128636094aae048809023aab811b25008d01284680342364a0114f4408a324043d5702164a010af4408561c042809821404810a620083aae040c94020587010292c0813250409904204c4010355c07f92803fbd381fde920fef4407f61c03fa4b01fcc7c0fe63507f31003fa5301fa4a00f8f4407caae03d49401e9e880f4c3807a4a703d25081e92580f555c07992803cbd101e58700f295a0794a703ca5081e527c0f293007801a03c55701de4a00eef4407761c03ba4b01dc09c0ee04207701503b80a41dc0500ee0110771b20398d601cc6800e6334073928038bd101c46280e355c06f928037bd101bd8700de92c06f32703799081bc6280df55c06d928036bd101b58700da92c06d32d03699381b4c840da63606d31503698941b40540da35406baae03549401a9eb40d4c3806a4a083524dc1a92580d464106a3100350cd81a86320d431406a02503501041a80540d401e06a00403519301a46900d355c0689280343d381a1e880d0c380684a783424d41a12580d06350683100340d381a067a0d033106818c8340c541a06280d003e06801a83400ac1a00540d001e068004034557019a4a00ccf4406661c03325381992840cc63606618a03300741980380cc008066aae031d57017e4a00bf25005e7a202f557016a4a00b4f4405a61c02d55701664a00b2f4405961c02c98801646280b12500577a202bb0e015d2580ae34305719b82b8c5015eab80ad2500567ad02b31041598700ac92c05618a02b004815a4a00aaf4f0557a282abd1015589e0aac4305561f82ab0e41558700aa92c0551a782a8d0c15466e0aa31405500902ad5701524a00a8f4e0547a202a316815189c0a8c3805449602a0c501500240a92500537a7829bd1014d89e0a6c4305361c829b0e014d2580a634f0531a18298cdc14c6280a60120539280293d101486280a52500517a7828bd1014589e0a2c4305161c828b0e01452580a234f0511a18288cdc1446280a32500507a78283d1014189e0a0c4305061c82830e01412580a034f0501a18280cdc1406280a0012050aae026803012aab8093250049006824c940121e8809006004702a0230120114cc808865804431a0220c7011001808755c0429280213d1010987008401d0420068213d34105e88082c380411a68208c50106ab808125a0407ad02030e01012580803490401a08200c50102ab807f25003f7ad01fbd380fd87007e92c03f19e81f8cd40fc62807f25003e7a201f0c500faab807b25003d7a201eb0e00f4cb407a64e03d32101e8c500f6ab807925003c7a201e30e00f009c07804203caae01d0d540e80aa075250039aae01c3d340e1e8807035503802a81c55700de4b406ef5a037aae01b3d680d803406c00e03692801abd3c0d5e8806a01b03500781ab0e00d24a0066c3803319e819bd100c9886064c3903261c0193d100c587006355c03092d0183d680c187006092c030aae017c9400bdeb405ef4e02f7a2017b0e00bd25805e65a02f3270178cf40be4a005cf4402e32701719080ba4a005af4f02d7a2016b13c0b588605ac3902d61c016a4b00b6ab8058f4d02c7a201631340b187005864d02c31001601540b2ab805725a02b928015b1040ad87005692c02b32081598800ac09205755c02a9280153d680a9e9c054f4902a7a201531380a987005492c02a31a81518800a86b405434e02a01e81555700a587005292c0293208148d680a46b005234c02919a0148ca80a46500532500287a2014557009e4a004ef4402761c013a56809d29c04e942027496013993809cc8404f55c0269280133d1009987004c92c02632d0131938098c8404c63e02631b01318a80980b404c04e02602101300a809801c04d2500257a7812bd1009589e04ac4302561c812b0e009528604a937025496012993c094c8604a637025315812988009409e04a04302501b81280cc09405604a01f0250078128024096ab8048c3802432081218800900b40480340240140120078092ab80472500237a2011b0e008cc4004605a023027011810808c01004755c0211aa810c940082ab803ef4d01f7a200f8d5407eab803d25a01e7ad00f5570075eb403a01a01d92800e3d3c071e8803801b01c00780e30e006e4a0034f4e01a7a200d30e006929c03433d01a7a200cb10c065872032c380197a200c30e0062ab802f25a0177ad00bb16c05d87002e93701749600bd57005a4b602d2500167ad80b3d68059e9e02cf4e0167a280b3d100598b602cc380164a780b250c05926e02c92c01632d00b193805868602c33f01619e80b010c05a4a002af4f0157a280abd1005589c02ac4201561c00aa508054c9c02a64201519880ac940051e9e028f4401462780a310c051872028c380144a180a24dc05125802955c0137a6809bd1004d89a026c38013326809990c04cc6e02662001302b809d57004a4b602525a01292880949400498b6024c4f01262080930e004929e024937012496009196c048c9e02464101231b80918ac048c4002435b012027809012c04aab802325b011928008bd6c045eb4022f4f0117a7008bd24045e8a022f4401162d808b13804587002294f0114a1808a4dc04525802265b011327808990c044c6e02263501131580898800446b602235a0111a78088d3804408602203f011aae00830e004126e02092c0103208080d680406b002034c01019b0080cd004065402032801000880800400424a001ef4f00f7a2807bd1003d89c01ec4200f61f807b0e003d29c01e94200f327807990c03cc5201e62000f1a78078d0c03c67e01f55c00e92d8074940039eb601cf4f00e7a28073d1003989e01cc4300e61c007256c0392b401c94f00e4a7007250c03928401c93f00e49b80724d803925a01c92c00e32700719080386b601c34f00e1a18070cfc03866e01c02b00eaae006c96c0364a001af5b00d7a7806bd14035e8801ac4f00d621806b0e00352b601a94f00d4a1806a4dc03525801a65b00d32d006993c034c9c01a64300d32100698f8034c6e01a63600d31580698a80340b401a04e00d02100680fc03406c01a02a00d009006803c0364a0018f4f00c7a2006313c031886018c3900c61c006250c03126e01892c00c327806190c030c6e01862b00c310006013c03008601803700c01980600ac03003e01801300c0078060024032ab8016f4d00b7a2005b0e002cc9a01664300b31b805988002c6aa01634d00b1a18058cdc02c63e01631500b18a005d57002a4b601525a00a9288054940029eb4014c5b00a62780530e002929e01494100a49b80524b0028cb601464f00a32080518dc028c5601462000a1ad8050d3c02869601434900a1a08050cdc02865601431f00a18a8050c500280b601555c00992d804c940025eb6012f5a0097a7804bd38025e8a012f4400962d804b0e002529e01294300949b804a4d402525801265b009327804990c024c6e01263500931580498800246b601234f0091a18048cfc02467a01233700919a8048cac02463e01231500918a004816c0240b401204f009027004d570021870010621008310004016802006c01001e008928003bd3c01de8a00ef44007627003b10801d87000e64f00732180398a401cc4000e34f0071a18038cfc01c66200e32900718f8038c5401c62800e04f007021803d57001a4b600d2500067ad8033d3c019e8a00cf4400661c003256801929c00c94200649b00318d80186b600c34f0061a18030cfc01863a00c31500618a00355700164b600b2500057ad802bd3c015e8a00af44005627802b10c01587000a95b0054a7802a50c01526e00a92c00532d8029968014c9e00a64e0053218029908014c7e00a63700531b00298ac014c5400a62500531080298800146b600a34f0051a18028cfc01466e00a3360051958028ca801462a00a31400502d802813c01409c00a04300502100280dc01405400b55c00492d8024940011eb6008f4f0047a28023d1001187000865b004327802190c010c4000831e00402d002016001009c00804c004021002010001006c008034004014002557000e4b60072500037ad801bd3c00de8a006f4400361c001996c00cc9e00664300331f801988400cc4000635a0031a70018d0800c66c00631e00300d001c940009e9e004f44002627801310c009872004c380024a180124dc00925800464f00232180118dc008c560046200021a78010d0c00866e0043330021958010c7c00862a004314002019801003c00a4a0002f4f0017a2000b13c005886002c3900161c000a50c00526e00292c001327800990c004c6e00262b0013100008d3c0046860023370011998008cac00463e00231500118a000813c00408600203700101980080ac00403e002013001007800802400401000207f000),[],(dagLookupLinks 0x267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099d0133a0267404ce8099b873370266e04cdc099b813360666a0ccc05998013300266004cbc19978132f0265e04cbc09978132c0e65804cac19958132b0265604cac09958132b0265604cac09958132b0265604cac09958132b0265604cac09958132b0265604cac09958132b0265604cac09958132a066520cca40994033260a64814c84398f8531e0663c04c5c798a853150261e34c3c09878130f0261e04c3c09878130f0261e04c3c09878130f0261e04c3c09878130f0261e04c3c09878130f0261e04c3429868130d0261a04c3409868130d026141cc2809850130a0261404c2809850130a0261404c280985013070e60e04c0c4981813030260604c0c0981813000e60004c00097e872fd025fa04bf4097e032fc025f804bf0097e012fc025f804bf0097e012fc025f804bf0097d832fa065f404be8097d012f9065f204be4097c812f9025f204be4097c812f8065ee0cbdc097b812f7025ee04bd8197b012f6025ec04bd8097a832f5025de34bbc0977032ee025da0cbb01975832eb025d604bac09728d2e5025ca04b940972032e4025c60cb8c0971812e2065c404b880970832e0065c004b80096f832df025be04b78196f012de025bc04b78096f012dd065b614b6c096d812da065b404b68096d012d9065b00cb60096c012d8025b004b60096c012d7065ac0cb541966912cc0659414b202963832c70258c0cb180962052c10e57c1cae8495b872b50a56a04ac83957872af0255624a9c4951892a30253c2ca64594c032970652c0ca58094b012960252c04a5809490928e1251c04a3809448b2841650804a082941012820250404a0809410127e124f4249e8093a8b275024ea049d409380b26b164d6049ac09358126b024d40c9a809350126a024d4049a809350126a024d4049a809350126a024d4049a809350126a024d4049a809350126a024d4049a809350126a024d4049a809350126a024d4049a809350126a024d4049a4193481269024d00c9a0093401268024d0049a0093401268024d0049a0093401268024d0049a0093401268024d0049a0093401268024d0049a0093401268024d0049a0093401268024d0049a0093401268024ce0c99c093381267024ce0499c093381267024ce04998193301266024cc04994193281265024ca04994093281265024ca04994093281265024ca04994093281265024ca04994093281265024ca04994093281264064c804990093201264024c804990093201264024c024970492c09258024a82494049280124c1249804920492401244124880491009220124402488049100922012440248804910092201244024880491009220124402488049100922012440248804910092201244024880491009220124402488049100922012440248804910092201244024880491009220124402488049100922012440248804910092201244024821c9040920812410248204904092081241024820490409200323d0e47a048e4491b852360646c048d8091b012350646a048d4091a812320e464048c809178722f0245e048bc09178122f0245e048bc09178122f0245e048bc09178122f0245e048bc09178122f0245e048bc09178122f0245e048bc09178122f0245e048b039160122812450048a0091401224124480489009108722102442048840910812210244204884091081221024420488409108122102442048840910812210244204884091081221024420488409108122102442048840910812210244204884091081221024420488409108122102442048840910812210244204884091081221024400c88009100122002440048800910012200244004880091001220024400488009100121f0643e0487c090f8121f0243e0487c090f8121f0243e0487c090f8121f0243e0487c090f8121f0243e0487c090f8121f0243e0487c090f8121f0243e0487c090f0321c0a43804870090e0121c0243804870090e0121c0243804870090e0121b064340c864190b852150a4261484429078520d0a41a0481c690303206023fe3c7fc08ff811ff023fe047fc08ff811ff023fc0c7f808ff011fc0a3f60c7ec08fd811fa063f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fd011fa023f4047e808fc831f9023f2047e408fc811f9023f2047e408fc811f9023f00c7e008fc011f7063ee047d818fa831f4063e60c7c428f7851ec0e3d4147a028f3051e6023be3c77428ee811d61e3aa0c75408ea811d4063a60c74c08e9031d2023a40474808e9011d2023a40474028e7051ce0239a0c73408e6811cc063980473008e6011cc023980473008e6011cc023980473008e6011cc023980473008e6011cc023980473008e6011cc023980473008e6011cc023980473008e6011cb063940c72808e5011c9063900c72008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c8023900472008e4011c80238e0c71818e2831c4063860c70818e0831c1023820470408e0811c1023820470408e0811c1023820470408e0811c1023820470408e0031c0023800470008df831be0637a0c6f018de011b61a36a0c6d408da031b402368046d008da011b306366046c818d9011b202360146c008d8011b002360046bc18d7811af0235e046bc08d7811af0235e046bc08d7811ae0635c046b808d7011ae0235c046b808d7011ad063580c6ac18d5031a9063500c69c18d3811a70234e0469c08d3811a11a3420468408d0811a1023400c68008d0011a00233e0c67818ce8319c063360c66428cb851960632c0465808cb011960232a0c65408ca811950232a0465408ca81195023280c65008ca01194023280465008ca01194023260c64c08c981193023260464428c8811910231e1463c08c78118e0631c0463808c70118e0231c0463808c70118e0231a0c63408c68118c063180462c18c50318a023101462008c4011880230c1461808c283184063060c60818c08318006300045fc18bf81177222ee045d038b88716f0a2da145ac28b389163122be2456c48ac071560a2a81454438a68914d022980c52c18a503149062920452408a2891450228a0451408a2811450228a0451408a2811411228204504089e0b13c02278044e8289d0113516262244c4089881130062582449c5893811270224e0449c0893811270224e0449c089381127022462448c088f0b11e0223c04478088c8b1151222a04454088a81111122182c43008860110c022121c4240882891050220a044140880890fe0e1fc043f8087f010fa121ec243d808788b0f1021e2043c408760b0e8121d0043a00874010e4121be2c37c086f810df021be0437c086f810df021be0437c086f810df021be0437c086f810de061bc04378086f010de021bc04374186e810dd021ba04374086e810dd021ba04374086e810dd021b41c368086d010da021b404368086d010da021b40435c386b810d7021ae0435c086b810d7021ae0435c086b810d7021ae0435c086b810d7021ae0435c086b810d7021ae0435c086b810d7021a81c350086a010d4021a804350086a010d4021a804350086a010d4021a8043443868810cd1219a043340866810cd0219a043340865070ca021940431c3863810c70218e0431c0863810c70218e0431c0863810c70218e0431c0863810c70218e0431c0862850c50218a043140862810c20e184042f8485f010be0217c042e8485b870b70216e042dc085b810b70216e042dc085b810b70216e042dc085b030b60216c042d8085b010b60216c042d4185a810b50216a042d01859830b302166042cc0859810b3021640c2c80858050ad0e156142a42854810a5121402c27c184f8109a1613404268084d0109a0213404268084d0109a0213404268084d0109a0213404268084d0109a0213404268084d0109a0212c24258084b010960212c04258084b01095061241c24808470908e0211c0423808450908a021140421c3843810870210e0421c084189083021060420c0841810830210604208184101081061000c1fc183e8507d020f80c1dc583b81077020ee041dc083b81077020ee041dc083b81077020e42c1b848309b05e0e0b22c15838290904a2208e1c104681d0f0370e06234088f80e8b00f3a00c4bff887fb10feb2dfd40bf9c37ef90fde05fb033f2cd7e190fbc1df5a7beac27d484f9f29f381be38e7c682f8131efe13dd4a7b41af650deb06bd6007ab04f5601e9463d28079e1cf3c01e6453cc4179880f3005e466bc7857881cf0f05e103bbecd77d80eee35dda0bba8376e9aeda0ddac23b4457660aebe39d5c83aa8474e9ae9035d027b9d8b73614e6325ca683944272688e4035c78238dc571a06e310dc5c1b8b0271504e270dc3663868170718e0e01c122b82406fe1adfc01bf8037c8a6f396de701bce0376cc6ed80ddb01b9a7371c66e302dba31b74036e416da88da63db4a0b660d6cc00d950db2a0363486c098d7e0dad69b5ac06b016d5725aae0355816ab00d473da8a13500569f82d3e05a569b4a8168d20d1905a282b44c168416d0609a04233e0a67714cea119be5b354a66906cc6319726b2e016588eca7299307b234b6401ac74318e8031c436321ac62098be1b178162d08c58098aa1b14c262806c4b158901b120062400c4411870630dc161598c2b0185213098360c9ac190183203034c60680c0b0981603004a60002bf4317e022fc005f58abeb017bc6af40e5df24bbe0177a0aef015db8abb70176e02ea4e5d306b973d72a12e4835c786b7e456f812de825b61cb6a096ce1ad8c45b006b513d6a202d10d5a200b363966c02c95158c1ab18016166ac2c057e9cafb095e83abb0857582ae9095c43ab68856c82ac64d57072a8d554c94a902550c529b9853310a5a3148e9a8fc851998a234142a7280154fe089f6193e032798a4f1089dc193ac32730a4e4089c50d3802a6f044dc089b70536a126cc24d4169a21933e1a67c04ce8499d013361263cc4c11a982012fc225f804b81c960412be0a57c04a81e950012962a524249e1a93b05276024b4e494889260d2326a458348a8290e1d2026a3bd24748c8e60d1c0323704466208cb0517a722e444559c8ab011501a2a0044e1889c011188223004409687f090fe021fc043d0a86c390d412194543280865010a88a14044211c83e11070320dc14180e82239040120257402887ff18ff621fa523f4807e414fc801f4d13e8847cf08f9c09f2843e4827c804f8821ee4b3dc807b804f5861ea823d3867a40cf4609e8813ce8a79a0cf3401e6803cb0879210f1e19e3c03c68478328f0601e0c03bd9077a04ee051dc003b78276e04ec851d7083ad8274f30e8661d00339d0c73a00e7011cd823988a72728e4819c6c93861e70b04df681bec037c846f60cdc891b882370046d13cda201b3053630c6c504d7069adc135a066b304d4e61a94234b9c69310d2601a4033480068820cf8619e433332666600cca0998c232f0a65d04cb02995c13261664c00c76898ec031d026274cc4a118397307006032cbf2517d442f5165e610bc22977442e9165c828b88216fc52dd0a5ad34b465168812cd8e59128b04795dcb2b51a5670cab661538d2a38e5440ca76494e8129c8253708a5a514987291865200ca3a19464428b0650c28a08413e8a277964ec0c9c64937462671e4c13496281294c24d94491288fe911f4223c8846a3c8c441158c2239e442148687109cd20d1a408487fa58fe831f7963de4478cc0ef881da923a05470ec8dc171abb23415865aa0c519181a22eb605aca8b151155b4283a04d4c894d711bb820fa03bf8072560d6b8185a02b1684e20090300f8a0197683107055b2095580cb8013d601da802264003080001 0x4203d10ff4c383b0a4b10a03583fc98810a1250427bd1109cc383fc1880f9031e3fb0c5107ef443fab0e0ec092c427013107033441b8cd101e01c426996108e31c424990108c31c42599310906404228c7109464c4220c70ebe008426c941098f44425b0e109492c42118a90723363af0021092f4442430e108f2504233d1108ac3842224b108262a4218c5108434c42080410812503fa30e0eba92c4204940fe6c383ae24b108125041fbd10fe4c383ada4b107ef443f8b0e0eb492c41fbd10fe0c383aca4b107cf4c41a190106664041898d10603344178ca105c63441e8d5107b25041db0e106c92c4061880eb0314407002101c04c4070130f9e03541e0d61079250406b0e107492c41a9880ff63143ab802106864c419190107604841d013106264041c8d310603404178d0107035841b8d3106c04841a813105c64041a3131066c4c4193101069250419b0e106492c41898810603414170c50f9c0413ab0021062940418253105e328418310105e3404172500fa00404152561038628415a56105294c40d98a105065841118d102e31c413993104263440b0c7105a01c413193104063440a8c7104a64c40a0c7105892c4059880eaa314415a4b10146203aa0c51059250415a4b10126203a98c5105492c41419050106203a90c5105292c41318d500e6203a88c51055250414a4b104a6354031880ea0314414494104ec3841324b104a6203a7802100a620402188100662041224b10446414011880e9c314411a4b10406354009880e9a314412494104692c40f98d50006203a60c51045250410b0e104092c40f9880e9600840f013103a03440e24b103462040b8d04ffe31440da4b103262040a8cd4ffc31440e494103692c40c18810283353fe8c5103525040ca4b10306204098cd4ff831440bc94102cc3840aa4b10286204098c51024048408812102004c407804101c04c4068131018048404256100a94040124d0ffe628405256100e94c400a4d0ffc628404a56100c94c401a4d0ffa628405c94101492c4049880e94314404494100e92c4031880e92314402c94100892c4019880e90314401494100292c4001880e8e3143ffc940ffc92c3fe9880ff83143fd4940fe8c383a2a4b0ff604c3fd4940fe6c383a224b0ff52503fabd10fe4c383a1a4b0ff20583fc0130fee04c3fb0160feaf443f8b0e0e8492c3fabd10fe0c383a0a4b0fe92503f9bd10e8092c3fa4940fe4f443f8b0e0e7e92c3f9c940fe4f443f830e0e7c92c3f8bd10fe0c3839ea4b0fde3143f780d0fdc64c3f730f0f940283f08d00f6a0103da0040fd864c3f318d0fd63403f28ca0fce6403f218d0fd26403f198d0fda6583f41900fda6203b38020fd92503f5bd38fd4c383f4a4b0fd06203b30020fcec383f34940fcaf4e3f230e0fc692c3f11880f6c0113b28020fc23343e72500f920283f018d0f660103e50100fbef4c3e70cd0f9a3343e60cd0f5e0103d70040fba6583eb18d0fb06403ea98d0fb664c3eb9900fa86343ed1930fa66343ef1960fb264c3ef1880ec80083eec940fb8f443edb0e0fb492c3ec9880fa23363b18020fb0f443ebb0e0fad2503eabd10fa8c383e9a4b0fa46203d90044ec40083e88d30fa0c483e78160f9c3403e72500f920403e68d60f9834c3e598d0f5a0103e50ca0f943403e480a0f920403d60c70f5631c3d50c70f5231c3d40c70f4e0103d30040f9004c3e38cc0f8c3303e28cc0f883303e3c940f8cf443e2b0e0f8892c3db9880ed20083e18150f840283e08120f800483df8130f7c0283de80f0ed20283d880a0ed20283d80108f783343dd8cd0f743343dc8cd0f792503ddbd10f74c383dca4b0ed03143a30020f706243d60ca0f563283d50ca0f523283d40ca0f4e04c3d98100f4c0403d680d0f4a31c3db8090f6c3283d98070f6a0283da0070f4e34c3d98d00f643283d68070f626243d898f0f600283d780a0f5c01c3d30d00f5a3343d60ca0f563283d50ca0f523283d38070f4c01c3d28c70f592503d5bd10f54c383d4a4b0f506203d38d08f4c3363d28020f1c6583c01930eee6403ce1960efe64c3bb1900efc64c3ba9900f1664c3ba1900f3264c3b99900f2e6583c49930ef66403b918d0f446583c41930ef46403b898d0f426583ca9930ef26403b818d0f406583ca1930f0c6403b798d0f263583c28d30edc3343c20d30eda3343c88d30ed83343c80d30f043403b58cd0f1e34c3c08d00ed43283d20040f466203d11880f426203d01880f472503d13d10f42c383d024b0f3f2503ce3d10f2e6203c98c78f3f2503cdbd10f34c383cb1880f2431e3cf3160f3a6343ce4940f36f443ccb0e0f2a6203c88c78f34f443ccb0e0f286203c80c78f30f483cbc940f2cf443cab0e0f2892c3c9c940f24f443c8b0e0f2092c3c78c50f1d2503c6bd10f126203c28c78f1d2503c63d10f16c383c41880f0831e3c6c940f18f443c530e0f0e6203c18c78f16f443c530e0f0c6203c10c78f132503c43d10f0ec383c324b0f0b2503c23d10f06c383c124b0f023143c04940efef443bd9880f012503bf3d10efac383bd1880eff2503bf3d10ef8c383bc9880efaf443be30e0ef06203bdc940ef4f443bcb0e0ef092c3bbc940eecf443b91880edc31e3bbc940eeaf443ba30e0ee26203b68c78eed2503babd10ee6c383b81880ed831e3ba3d10ee6c383b79880ed631e3b94940ee2f443b830e0ede92c3b74940edaf443b630e0ed692c3b50c50ed20283b400a0ece3583b30d00eca3283b20d60ec634c3b10ca0ec32503aeb0e0e8a92c3b0c940eb8c383a224b0ec32503b03d10eb6c383a1a4b0ec0f443ad30e0e8492c3b03d10eb2c383a0a4b0ebe3583af0d30ebb2503ae3d10e8092c3aec940eb6f443ad30e0e7e92c3ae4940eb6f443acb0e0e7c92c3ad3d10eb2c3839ea4b0eac3343ac0120eae04c3ab0d00eac9403a91960e9c6343aa1960ea264c3a698d0ea66583a81930e9e34c3a58ca0eab2503aa24b0ea66203a50c50ea52503a8a4b0ea06203a78cd4e923143a40c50e9d2503a6a4b0e986203a58cd4e8e3143a51960e9264c3a418d0e8e6283a300a0e8b2503a23d10e8092c3a2c940e86f443a130e0e7e92c3a24940e86f443a0b0e0e7c92c3a13d10e82c3839ea4b0e8125039fbd10e7cc3839ea4b0e7802839d0cd0e7233439b80a0e7633439b0ca0e7631439d4940e7292c39c1880e6e33539b0c50e3494d36d24b0afc62027b0d3457e31436ca4b0e6a32a39a004457c0083974940e2ac4f36c30e0d3494f309a4dcbb892d2be24b095c64f20c98dc7d662b1ad989c5f662115e1880dae92c2bd988057631438c9904dac6202bd0c509e804115d0020daa92c2bc988057231436a24b0e6632a399004457000838a2564da692c34b9964d6464d3451904aee6202568d6456c3143691880aec31415a8020e246413689880d123352ba8c5095604115a0020e18c4d36830e0d0e94d2ba24b094a64d1599880e62326367a4b0ae66201590c50e6355c38f30e0d9c92c1588c50e6002a3978048e5d25038c313cd9ac38358253cc229372ed24b4ae292c279993c8306371f498ac6b462717c988455e6203968c9ce5231b38ba504d9892c2b818809e23411570c50e5d25038ebd10de6c43365b0e0c5694330824dcbb292d2b7a4b087264320b98dc7d062b1ac989c5f06211569880e5b55c38e3d10d94c382ec24b05586203960108e560363950078b22008394d570e36f442b724b07cc62a3940160e4e04c3930108e4a02a378a534d9292c3149934c426352b6188086e34d2778d045543143924940de094d37624d4d9092c3141934e4464931018d4ad662021b0d349483411548c50ad43143924940ad26203918160dde941375a4d4d8e92c3139904c3e6352b4188086a3411540c50ace3143914940d8c92c3908d38e4032a38f804454e00838ebd10e16c43362b0e0d0a94330724dcbac92d2b2a4b094464320b18dc7ca62b1ac189c5ec6211531880e1494d36224b0d0864d3569904d026352b2188094234d1528c50e10c41361b0e0d009412b1a4b093e6411521880e3c02638ebd10e2cc4336130e0d58943306a4dcbaa92d2b124b09da64320a98dc7c862b1ab989c5ea6211519880e3802738d806cac26201510c50ac06201508c50e28f5938c3d10e0c9423061964d5664d2fa98a4abe62020a0d649d834d1500c50abc314275810453e00838d5570e32c4d3893104e2ec3838298d8d5435935f8d34be831d2ae8c509d4059287813482404124f00dc53c00838cbd60e3155c38bbd68de2c4d38b30e0dd49363051934d506412f998a4ab86202088d349d034114e8c50dd264037398a0e14c4d38b30e0e069363049934d4e6412f918a4ab66202080d349ce34114e0c50e2b55c38a4968e232503863d10e0c95a3041934dfa64933e9904bdc6292ad188081e34d24e8d045363143893d30e0a64c24e00d4e2b55c3884940de0c4d385b0e0dcc9363039934df864933e1904bda6292ac988081c34d24d8d045343142ac0c5053200838a5570e272503893d68e1492c37298a8c0c34d3528d04cf63352f60c74aae3142068134530008388d570e21250384b0e0e0e95a3822538dc893633d1904bd66292ab188093434114b8c50e1e04e3870078e1a0123865570ddec4138430e0dc69363019904df663d2f518a4aaa6202058d0452c3143711960dc0628385c940e14f4e384bd10e10c38381a538c0464137d18f4cee6352f498a4aa86202050d0493033514a8c50e0ec3833b0ca4aa631424b80a45280083835570e0af5a38230e0dc464d37498d4e066202f40d34d483412f88cd4cea3292a90c509ca04124b00a45260083810cf0e0464c33a1900bc86283808d90e0035837f8cd0dfc01037ed570df925037dbd10df4c3836fa4d8cfc64237c8d60df034e37b8d30dec33437a8044de80101490020de72503783d38ddcf443763138dcc94e2ff9904dbc63d30e98d4aa06202048d048643352038ca45223143729960ddef4c375b130dc694c379c940de2f4e376bd10dd494e2ff1904dba63d30e18d4a9e6202040d048623352030ca452031437900f4de2c3837118d8a9c3143784940ddec383749938a9a3143774940ddaf443742538dc29422a61880dd9250375b0e0dce64e37018d8a96314372b134dd4c38374a4d8dd092c37398d8d463412f80ca4c3631d2a50c5080a04d272010492a037218007451e0083734940dcaf4e3723d10dc6c383712538dc292c37018d8dbe33d3398cd4bcc32930d0c74a923142020104928035217807451c00836f4940dbaf4436e0d38db634236c4940da6f4f3683d14d9af44351253cce494332d24fcba692d2a3a4b09c664f249990c7c462b1469880db555c3693164dacc4d368b104d98c383509964db265535e1934a8c6202710d64a1a34d2700d0451831436c4940daaf4f365bd10d90c43362b0e0d7694f338a50cc329372e924b4a8a92c286193c92464321718dc7c262b1459880daf55c3693d64dacf4d36abd10d9ec383381964da865535d1934a886202488d64514314369d570da525a368bd68d8892c3379934d3e64133618d4a866202480d345123143685570d9ef5a363b104d86c38335a504a8492c24719045106203670098d9b2503663d3cd96f44364b10cd84c3835ca53cd3c94330c24dcba292d2a0a4b0a1664f26f990c85a6371f018ac50e620365009cd92c382a01880d91250363b0e0d8c63d29f9880d8af44362310cd86c3936130e0d3a94333524dccb29332e824b4a7c92c26f190c91a6371ef98ac50c62035ea4b050a31436080a8d8001235f9904d786202e78c509b80411420020d7692c2e7188050631435d1880b9a3141410020d7292c2e618805023142e58c505000083553d90d7ef5835f3d80cd033424580d4d7b55c350bd64d78f4d35dbd10ce0c5935d3134d72c3833398d8b946201ee0d64a0834d13f8c50d7004c35bd570d2ef593593d34d60f443062564d5694d35124b0cca6422e498807b63592658d344fa3143551904d426202e40c5099404113e0020d6f55c358bd34d5ef4435730e0d5294d35024b0cc86422648d344f631435b0134d6a04235a00a8d660123595570d62f44356a4b0d4a64d34f9880ccc3353310cd0b8e31424481344f40083585570d5f250314b134d58c383052534d5094134f24b0b8c6201ec8d3498e34113c8c50d5d2503423134d5ac4135630e0c1294d353a504d3a92c33098d8b8a6201ec0d3498c34113c0c50d5755c3553d68d52f44352b134d50c38353a4b0d4863635198a8cc03362f18c74b8831420181347ac04113b8020c0cf583533d50d4af4c2f41960d4864c32f8cd0d4664c3515570d4325a3504940cdec4d34fb104d3cc3834ea4b0cbc6362e198807aa34d2628d044ec31434e0120d383582618d30d360641990130d3555c34bc968d2b2553494940d14f5a343bd10c1094d33ea504ce492c3329968cb063d2e118807a834d23b8d044e8314344b130d3555c348c940c50c4d342b0e0c0e94d33e2504ce292c2e098807a634d23b0d044e631434c8128d300483381880b803141390020d2f55c34b4940d0892c3031934cde6202df8c507a404d1388020d2b55c34a4940d0c94d341a4b0cfe64d33c98d4cdc6202df0c50cba04d32e01248ea0351380020d2925423a0d04d260583495570d232503443d38baef4434130e0cf0941336a4b0cd265a3319938cae63d2b918808e63411378c50d2004e3478134d1c04c3468104d1802a3458048d1555c344bd68d10c38340a4b0cf664d3361880ccc3413310d00b7a31423901344dc008343d570baef44313b104d00c38301a504cd692c2de188079e3411368c50d0cf54342c940d08f4e341bd24d04f44340b138d00c383012504cee93533524b0cc264e32b18c4b766201e70d048e03351360c50cec63423780d4c0cf5833db160be264033a98d0cc034c33fbd50cfc34833ed570cf925033dbd38cf4f4433cb124cf0c3833ba4b0cec65a33a9938ce662a3340d68cbe34e33a0cf8bc431d2dd0c50a0605b20101047980351358020ce66403395570ce32503383d68cdef4e3373d24cdaf443363138cd6c3833524b0cce65a32f1938caa6312dc98807963412370cd44d431423680d4cd2c383340ca4cce31423600a44d20083333130ccb55c3324940cc6c383312500cc26203300d04cbe32932f0c5098204123580a44d000832ebd50cb603c32e4950cb634c2348d0063404032d30e0cb094d2dc24b0c9e6583251900c8e63632118d0c7431d31a8c704cc31432cb0e0cac9412dba4b0ca46583271930c8c63632098d0c7231d31a0c704ca3143288d90c9a3583220ca0c6601032d5570cb2c3832aa504b6c92c32a1968ca06583261930c9063431c0c74c6431c1320c50cb155c32bbd10cacc3832aa4b0c9634c3218ca8c7a32831b0044c5a0101318020ca86202da8c504c4008329c940ca492c32898acca062030b8cacbc231f2da0c5085802b200807c75601317880244c2008327c940c9c92c32698acc986203258cd4c2c32b2f00c7cb6631421580ac80001f1d5004c5e00091300020b643143254940c9292c3241880bbe31f2d88c5075201312f8020c8f55c32330e0c8a92c32218d8c863412ef0c74b603141ff80a47fc01d12f0020c85250320a4b0c8062b31f9884c7c62031e8cd4c2a32b2ef0c7cb5e31421500acc7801f31d806c75001317780244ba00831d5570c72c3831c24b07fe62a31b9880c6c3412d70c508520361fe80a86e20121770020c6b25031a24b0c6662b3191880c6232b3180c7cc5e3153170c50c5a03530a00acbba01f1b8804cb5a008315c940c50f4e312bd10c40c4e2ffa504c3a93530ca4b0b586201e48d048483351d38c744b8314313bd30c3ec4c31600f0c57250314bd38c48f44310b138bfc94130e24d4c3092c2d598807903412118cd474c31d12d8c50c5403d314b0e0b543143144940c4ec382d48c50c4c634312c940c48f443118138c44042310b0e0b503143104940c3ec382d38c50be063430d98a0c3cc482f318d0c3462830ec940c38f4430d9938c346422d30c50c3325030c3d10b4a62030b8d90c2c35830a8ca0c28010309d570c232503063168c10c4e2feb0e0bea95a2f72538b486201e38cd47f83291d20c744b43142fa1930c2755c3084940c1cf44303b138bfec422fe30e0bda94e2d1988078c3351fd8ca474631d12c8c50c0c9582f61960c06c4c2f52530c24030308d570c21250306bd10c14c4e2ff3108bf6c382f9a538b446201e28cd47f43291d10c744b031430780c4c1d250306bd10c12c4e3013108bf4c382f92538bd29422d098807883351fc8ca474231d12b8c50b4031412b0020c1955c305c940c0cc4d30530e0c1292c2f418d8b3e3141e1813497c04112a8020c0293c3045570c0f2503033d38c0af493023d10c06c3830124b0be264e2cf0c5078404123300d44a8008300b130c009402f39930bbc6282ffc940bfcf442f81938bcc6422ce8c50bfb55c2fe4940bf6f442fd30e0bde94e2f2a5087f03291d00c744a63142fc8138bf00422fb80a4bec0122fad570be8f5a2f63134be6c382f924b0be26362f818a8bde6202f18d04b383141fb813497a0411cf80444a40082f75570bdb2502f63d38bd6f442f530e0bd292c2f41938bbc63d2f398c4bcc62a2f29880bc833e2f10cd4b363141fb01048ca0351cf00444a20082f19930bc46402f08d90bc03582ef8d00bbc3282ee8040bb955c2ed4940ba6c382e4a568b8494e2dc2528b489361ce18a46ac6251281880b3235a2c98d38b143362c28c78b906642e79960b3004c2ee5570bb32502eb3d10ba4c382e72568b8294e2d62508b469361cd98a46aa6251279880b2434e2c60d08b123362c20c78b806642e69960b7e6582e39930b7a6402de2530b2234c2ed8030bb555c2ecc940baaf442e8b0e0b9895a2e32538b569422d124d87346291aa189449c6202cb8d38b163422c40cd8b0631e2ec0094bae00d2d51960b506342d49930b4e6342eb4940baaf442e830e0b8a94e2dda508b6e93e2d0a4d87326291a9989449a6202cb0d38b203422c38cd8b0431e2d01990b966582cf9960b8864c2ce18a0b3c64c2dd1900b366282ea0120b3a6402d318d0b0c0282e9d570ba52502e8bd10ba0c382e52568b8694e2dca508b6c93e2d2a4d87306291261880b3435a2ca8d38b1e3422c08c78b90f592e7bd34b9cf442e03164b9ac4d2e630e0b406592e59934b946201cb8d64a0434d1258c50b1c0362e4d570b9125a2dfb134b8ec412e330e0b5494d2e2a4b0b3e64d2e21904b866201cb0d349783411250c50b1a0362e15570b832502e03d68b7ef4e2df3d24ae4f442deb138b78c382d4a504b7692c2cf1904b746352dc988072a3412320cd44923142ca0138b7155c2dbb0e0b6c92c2da9968b686582d99930b646362d898d0b6062a2d798a0b5c31d2d68c704903142d64940b56f442d53138b52c422d42538b4e9422ce98d4b4c6292d298807283352110ca448e3142c00048b4955c2d1c940b44f442d0b0e0b4095a2cfa538b3c9422cea4d8b3864e2cd99087263291fa8c7448c3142bf8048b346201228020b3355c2cc3d68b2ec382cb24b0b2a6202ca0cd84880082c9d570b252502c8b0e0b2092c2c79880b1c35a2c68d3848600828900a0b192502c5bd10b1555c2c4c940b10f442c3b0e0b0c6361c880444840082c2d570b092502c1bd10b04c382c0a4b0b006362bf98a843200828880a0af92502bbbd3cae8f452b8bd10abe94f2ad250ca8e92c25d193c8c464322098fc7e862b176188448062029d0d3ca6a3432980cfca4a32b2900c7ca3631b2bf5570aecc592bd3134aeac412b830e0abc6592ae9904a8c62025c8d64a0034d25b8d0447e3142be8154a720412be4940af2f4f2b7bd10ad6c432b2b0e0ac294f2aca50caa09372a2a4b09fe64f230990c8426371f998ac5d662111f1880a7a34f29a0d0ca503372920caca3e31f28d0c6caf755c2bb3d64af4f4d2bcbd10ae6c382ac1964a886202300d6447a3142bc0154aef55c2bb4968aeaf5a2b52534ac892c2ab9934a8662022f8d344783142ba5570ae6f5a2b43104ac6c382aaa504a8492c22e99044766202998d04ae400e2b8c940ae0f4f2b7bd10ad8c432b130e0ac094f2ae250ca9e9372a0a4b09fc64f25b190c8406371f918ac5d462111d1880a7834f29c0d0ca4e3372918caca3c31f28c8c6ca263152b7006cada00f2b53134ad8c382b3a4d8a9c64d2a0188083e34d25a8d044723142b5c940ad4f4e2b4bd10ad0c382b3a538a9a6412a598a4a7e62020f0d048b833511c0c50acc03d2b2bd10ac8c432b1b0e4ac4c382ada50caa893729f24b096864322d98dc8806331f898ac5d262111b9880a6e3432990cdca5e3332910caca3a31f28c0c6cabcf592b0bd10ab0c592b030e0aa66361f80d649fa34d11b0c50abf55c2af4968abaf5a2abb134ab8c382a72534ab692c2a918d8a9462a1f78d3496634111a8c50ab555c2acc940ab0f5a2abbd38aacf442aab0e0a9a9412aa24b0aa665a2a91938a9262a1f70d048b433511a0c50aa203d29700c4aa12502a7bd10a9cc4e2a6b108a98c382a5a508a9464e2a499087da33520e0ca47d831d1198c50a900312908074a8f2502a33d3ca8af442a2313ca86c432a130e4a82c382a0250ca7e93729f24b09f864f259190c8b263720d98ac46462029d8d3ca6c3432988cdca5a3332930caca3831f29ebd10a78c3829d988046231429d5570a72f5a29c30e0a6e92c29b188046031429ad570a69250299b0e0a6492c298988045e3142985570a5ec382972504a5a92c22b990445c6202960168a5603629500a8a5201e2944940a4ef44293188045a314292d570a49250291bd10a44c3829098d84583142905570a3f25028f3d10a3ac3828e24b05d031428dd570a3525028cbd10a30c3825819388ac64228b8168a2c04e28a8108a28036289bd10a246422888c7445431428724b0a0262028800d0a1e6412869880a0031425781045cc00828624b0a1465527f98805ca314285a4b0a1265527f18805c831427e8c509d4f64287bd60a0633522a00d0a1d55c2713d64a1af4d2863d10922c59285b0e07b86592841954a0864d27e18808a63362854940a12f4428424b0a0e34e2830d08a0a32a2821880a043141718020a0663522900d072e6642811960a0355c25cbd64a00f4d27fbd108c0c5927f30e07e065927e99349f86202288cd85c431427d81549f555c256bd649e6f4420a25649d894d271a4b07b665926b195499664d25d18808a03421c78c785c231427519049c462025c8c505c000827d55709eb25a2793d109e0c4d27730e09d294d270a4b099064d25c188089e3421c70c789f204227c00a89ee01e27b55709eaf4427a3134956c41278b0e09d665920919049c06202650d649b834d26a8cf496e314257813489c0361c680485be00827a3d609e755c27949409e2f5a21bb1349dec41276b0e082294d27425049be92c1ec99349a8649263990496c6201c60c785bc3142783d109dec3825a8c508980361c580488960341c500489dd250250b1349dac3820825349ce94126f24b07b064d269992498c64125a18808943361c48c785ba314275bd909d955c275c9689d4f5a274bd109d0c38273a4b09ca63627218a897c34d1eb0d0497a31d2598c508920361c4004881af582733d509ca64c22400d080a658272193088e042271d5709c525a270c9409c0f5a24831349bec3826f24b07aa64d269192498a641259188088c3361c38c789bb2602653d909b8f5826d8d209b665826219309b436426c8d009b033426b8ca070601c26b55709ab25a26a3d109a6c3826924b09a23582680d0899e3402670cd099a32a2660ca072001d16e002099755c26549689932501993d28990f44244b10498ec3826324b097c64d201990498a6202620cf898233625e0c5098604a22280d870401216d80207a4f582613d508e4c582608d3070c04022200d0980c5422181087020101e1a56097e95425f25307ee65825e99307000101cb196097864c1bf8c7097605425d557097325a25c494096ef5a22fb13496cc3820fa53496a94125a24b07de64d25999049646202210cd85b4314258812496000d257bd6095d55c256c968955250252bd1081e94d24ea50492692c1ea193490664923b99048c46202280d686f831e16c8c50956f4c24f1934938635227013095d55c254c94086cc4d2523104944c38207253493694124924b07a664d24119248ec64123098806f631e16c0c509226202300c505ae008256d570959250255bd6894292c20699349206201e90d349123412390cd48be3141bd00485ac008255557095325017bbd10946c4125030e0932941247a4b08e264122f18808aa35a2268d386f231e1580c5095004e25380a894c01e252d5705eef4421ab10493ec38205a50491c92c1e7990490263d22e98806f031e16a8c5089804c1bb8048949250251b0e08b831422581386ec0122514940942f4e2503d1093ec382052504930935246a4b079c64124018f48e063522d988089434e1ba8c785a831424b98d08de33524f499881af5824b18d092a62a224813093b55c24e496c93725024d3d10932c3824c24b092e65a24b193892862a2458d6c8cc3411e60cd48ca31d22d0c508a805a22401386e801224a996880864c24a190088e05a249d570925250248bd68920f4e247bd1091cc38246a4b079664123f98f48dc63522c98808a635a2230d386e631e2463d809166352368cd48d83341e93d60914f54244bd308d63341b9016088a04c2440cf091064c235190090e3642430d6090a3342420ca06d801c241d570905250240bd10900c3823fa4b08f064223f0d608fa34e23e0d308f633423d0ca88f23281be80745a60081bf3d308f033c23bd5708ed25023abd248e8f45239bd108e4c4e18d30f88e2c3823824b08de65b233190480463523718808da35b2360d688d634e2350cc88c8314229016888804e23480f86d601216900208d0c4822181686d40121b4804078494c233a5208cc9401fb19308ca6401b4004072a64c23219006ce31c23181208c555c230c9408c0f5a22fbd388bcf4422eb0e083c94122e24d48b692c1f719048b463522c98808a235a2210d385a231422c00f48ae03122b00348aac3822a0ca48a631422900a48a2008228557089f2502273d6889ac38226190489662922518808923412240ca488e31f2230c506e404d222810470c03522200a488601f221002088292c21e8ca888092c21e0ca8874328220d570880c3821f8d6887c33621f8c5087c31421ed570878c3821d988087431421cc94086cf4e21a3d1081294121924d485c92c1e4990485063d21218d48426201680c5086af4c21cc94086ef4e219bd10810941218a4d485a92c1e4190484e63d21198d48406201678c5087003d21bb0e083e31421b494086ac3820f0c50869250219bd1083a62021818a085e6282194940862f44218193885e64220e0c5085d250216bd108366202160d908563582150ca0852010214494084ef442130d3884a3422124940846f442110c5072864021118d08432502103d1083ec4e20f310883ac381f698d483862920d988059c31420d00c483355c20c4940828c5a207b13878e6351fe18a47e86201b30c7882494c20cd57082f25020b3d1081cc4e204b10880e9421e318d47f66291f998806ca31e206a560816c4c20c557082f25020abd10822c4e204310880c9421e298d47f46291f918806c831e20b494082af442083138814c421e218d47f26291f898806c631e1f80c5082955c209c940824f5a206b134822c3820824b080a62a1e18d348063411fb8c747de3141b1004881f55c207494081af4e2063d10816c3820524b080862a1e10d048043351fb0c747dc3141b080488132502043d107da314203c94080cf4420299388086421f60c506c00121e1a56080694c1e125308049402008d908003581ff8cd07fc3281fe80407f955c1fdc9407f4f441fcb0e07f092c1fb99387ec6421fa8c506bc0121ae80407266341fa98a06b831c1fa55707e72501f93d107e2c381f825687de94e1f725087da9361f618d87d755c1f4c9407c4c381eda5687a894e1e3a4d87809311db24b07486361ce188071e35a1be0d386cc3361a90c6859a3141c681307d755c1f449407caf441f0b0e07a694e1e4a50878c9361dfa4c476a92c1d399087466361cd98806f634e1b28cd86a231a1660c507a46581bd016079e94c1bc0d307d40241f4d5707d12501f23d107c0c381eca5387909421e2a4d877c9311da24b074c6421d118d87346201c60d386c83361a80c685963141f380947cc00d1c581306ee0421c501686ec0401f2c9407c8f441efb0e07b094e1e725087889361dea4c476692c1d098d87326201c48d386ea3421b18cd869e31a1650c507866581eb193073e3281b1016071004c1e119307c66481e6190073c3281b081306e80401b000a07c555c1f0c9407c0f441efb0e07b895a1eaa5387969421d924b07306201c38d386e63421ef00987ba0241de18907b86201cb8c505920081dd98907b755c1ed49407a4c4d1ecb0e07b092c1e199347ae64a1eb19047aa6201cb0c506e4036164002079463c1dd18907a955c1e9c9407a4f4e1e8bd247a0f441e7b0e079c92c1e1190479a63e1e618d47966201ca8c5070c04e163802079494c1dca4c06e004c1b880707932501e43d107283141e3d57078d2501e2bd10788c381e1a5387849421e0a4b07263141e0557077f2501df3d1077ac381de256877694e1dd250877293e1dc24b07243141c281386de0421dc24c06dc34e1db80d076d55c1dac940768f441d9b0e076492c1d298d873a62a173988070834e1b68d086be32a1a70c684823141d881387600421d780a875c0291d680a07580111c101306fc64c1b581007563641d50d607523401d40cd06e20101b5013874f2501d33d1074a3141c081386d20421af00a074955c1d1c940744f441d0b0e074092c1cf993873c6421ce8c5070004e1b401086ba01c1ce55707372501cd3d10732c381cc24b072e65a1cb193872a6421ca18d872662a1c918945ce6201bf8d386ce3421ae0ca858c3141c880a87203541c7d57071d2501c6bd686f4c4d1c630e07169411c524dc71292c1b119347106411c3988070c3361c28c647083141c181287040411c080a870001e1bf80206fc64c1be8d206f955c1bdc9406f4f4e1bcbd106f0c381bba53c6ec9351baa4b06c26411ba18d46e66201b90d386e233d1b80cc46de3191b70c546da3141b600f86d60351b500ac6d202a1b400786ce0081b355706cb2501b23d106c6c381b125386c29421b018d86be3141af00746ba01c1ae00206b755c1ad49406ac92c1a918a868a35a19e8d6065c34e1920d306283401840cd068604c191810062603418380a06b755c1acc9406b0f441aaa4b06a262a1a58d6065a34e1910d3062e3421890d0060c33419c813065404018880d060a028196016068404c194810062003418200a066c3581940d3061e3401818cd06b555c1acc9406aef441aa24b06a062a1a50d6068234e19a8d3062c3421870d006043341ac49406aef441a9a4b069e62a1a48d6068034e19a0d3064e34218e8d00602334199813063804018600d06000281a4019066404c18d810061603417f80a068e064198816063404018500d05fc0281ab55706ab2501aa3d106a6c381a68d6868c35819f8d3866034c1930d0863234018a8cd861233417e8ca06a555c1a8c9406a0f441a7b0e069c62019f013865e04c192810863004017e00a069a3141a64940696f441a530e069292c1a40d0c68e3371a30c5068b55c1a24940686f5a1963134684c411a0b0e068092c1990d0467e31419f004867b25019e3d3c676f4519d3d10672c4f19c310c66ec3f19b30e466ac3819a24b066634f1990d0c6623371980c5065e012197557065b2501963d38656f441953168652c4e19430e064e92c18d0cd464c3141928048649250191bd3c644f44190b13c640c4318fb0e463cc3818ea4b063834f18d8d0c63433718c8c5063001218bc94062cf4418a8c50629250189bd3c624f44188b13c620c43187b0e461cc38186a4b061834f1858d0c6143371848c50611250183bd3c60cf44182b13c608c43181b0e4604c38180a4b060034f17f8d0c5fc33717e8c505f801217dd5705f325017624b05c265a16c993859a62a1628c985c03641730d605be34c17dd5705f125017b3d105d692c17299685b064e168190859862a1620c985ae36416b0d605aa64c17d00305f355c17c49405eaf4417524b05c865a16f193859e64216598a858632617b80345ed25017abd105d292c16e99385a864216518a85843261648d905c635817a018059035816d8d305e60541638d305a434017901205e266417819605de6341770c7058c62810c80705da00c17655705d72501753d105d2c3817119685b464e168990859c63617400745ce00d1703d645ccf4d172bd105aec5917230e05923591718d345c4314170d5705c125a16fbd685acc4d16f30e05ba92c1640d345b834916d8d045b431416cd5705b125016bbd685acf4e1583d105aac3816a24b058e3411698cf45a43351688c505a1250167bd1059c314166d570599250165bd10594c38164996859064e16399084826201630c5058b55c1624940586f4416130e058204e160010857925015b3d3c566f45157bd1054094f14da50c51a92c13e993c4e864313318fc4b462b12818844806201148cfc44231b15fd57056ac5915d3134568c4115730e053e65914f190451862013e0d6457c3551420d3447e31415e815457925015cbd3c55af44154b10c54cc38151253c534943148a4dc51692c141993c4e664312e18dc4b262b127988447c6201100c6c57755c15abd64574f4d15cbd10564c3814c99645146201390d645703551410d3447a31415b815456d55c15ac968568f5a152a4b053064d14498804e234d13d0d044dc33511e0c5056755c1593d68550c4115230e052c94114424b04da64111d988056201a158003855f2501573d3c55af44155310c546c38150a53c53a94314824dc50e92c140993c4f264312d98dc4b062b127188447462010f8c6c55801b155803c554c3811c8c5055325015430e054e33d11c0c5054cf44152b10c548c39151b0e053894314aa4dc50c92c13c190c4d863713298cc4ae62b126988446e6201140ccc43c31b14fbd64544f4414cb164542c3814a18d84ac3591400d3446c314150557053f25a14f3d68530c4d14eb0e053892c14998d851e62a12a8d344ee3411290c7446a31414dd57053525014cbd68530f4e14bbd1052cc3814aa4b052865a149993851c62a12a0d0452433d1358cd44a231d11a0c505232501483d1051e64e1471908466314146c940518f4f145bd10514c4f144b10c510c39143b0e050c92c13f993c4ec64313518dc4c86331261884464620142d5704f8f591423d34506f441393164504c4d140b0e04ac65914019344fe6201348cd849631413f01544fb55c13e49684f7250138b1344f4c4113cb0e04f092c12a99344ee64113b18804d03361250c504ea04913a55704e72501393d684e2f4e1383d244def4413731384dac3813624b04a864113598d44d46201348d684d034e1318cc449231413380f444e03113355704cac3813224b04c664112418804c435a1308d604c034c12f8cd04bc32a12e8ca04b925012dbd1048e31412d55704b325012c3d104aec3812b25684aa94e12a25084a692c12919384a26421230c504a155c127c94049cf44126b0e049892c125996849464e124990849063e12398d848c62a10e8c6448a05a122013848604212100a848200e120494047ef4f11f3d1047ac4f11e310c476c3911d30e047294311c24dc46e92c11b193c46a64311a18dc46662b119188044c333118813c46004311780dc45c03311680ac45801f115803c454009114d570450c38113990444c620112816844803411180a044401e110d57044125010fbd1043cc3810e988043805a10d813843404210c802042d250108bd3c41cf45105bd103f294f0f9250c3a492c0df193c3526430c598fc2d862b0a7988425a6200830d3c1d03430610cfc14c32b0490c7c0c831b0270c5407431410c5570420c5910a313441ec4110530e03f06590fb99043e26370e8988037835910b8d5438e34d0d40cdc2d631f0a70c54258314082016422804d08081041ce037052807c122013031803c09a00901c802042d250109bd3c412f44102b10c3fec380fda53c3e09430eea4dc3a092c0e3193c34e6430be98dc2d462b0a698842566200898d3c1cc34305d8cdc14832b0480c7c0c431b0260c5407031410ad570420f5910a3d34426f44106b0e03dc6590fb190c3d26370e7988034a3591090d5438a34d0dc8d0c33e3370b48c7c2983150950c501c8059080010c1be037051807c11e013030803c09600901b802042355c108496841ef5a10225343fc92c0f619343b862b0e7188034634d0db8d0433c3350be0cac2d031f0a58c54252314071013417402b051007c11c013030003c09400901b002041d55c106bd68404c410feb0e03d09410eda4dc39a92c0ce99042f66370b398ac29462109418801bc34105c8cdc14232b0468c7c0be31b0248c5406a31410600684172501053d3c412f44103310c3f8c380fd253c3ea9430ed24dc39892c0e2193c36c6430bd18dc2cc62b0a4988424e6200890d3c1fc34305c0cdc14032b0460c7c0bc31b0240c54068314104006c40e00f102313440cc38100a4d83b264d0f398dc3966200bc8d343383370ba8ca42ca31f0a40c5424c31405b81341f804106e80dc116013019802040b2501023d38406f4410130e040294e0fa193c3b06410f298dc3ac6290e5188036834f0bc0d0440033d0cd0cdc2e83290b20c7c28e3150928c501f604f05b01041b603706d00d411401301900203fef440ff310c3fac390fe30e03e69430f224dc39292c0d9990c3326370c518cc2c662b0a3188424862007d0d0c1b23370608ccc13e32b0448c7c0ba31b0238c540623140fc3d643f6f440f731643f4c380f198d82c23590e18d343643430cc0cdc28a3150918c5013c05908881341f204306c00dc11001301800203f355c0fc49683eef5a0fb316c3d8c4d0fab0e03b294d0fa24dc3e692c0f118d83aa62a0e10d6c2be34d0d80d0432e3370b98cac2ae31d0a20c54244314088016c13a04d07b81041ae03705a00ac10e01301780203e555c0f8c96c3e12500f7bd6c3dcf5a0f6bd3c3d8f4e0f5bd143d4f440f4b16c3d0c380f3a53c3cc9430ec25043ca9370f224b03c665a0f119383a862a0e08d6c35e34f0f08d0c2ba3410f00cfc3be33d0ca8cdc3283350b90cac2ac31d0a18c54242314087816c1ec04f0ef010c13804106a80dc1a803505980ac10c01301700203bb2500ee3d3c3b6f450ed3d103b2c4e0ec31083aec380eb25083aa64e0ea190835c34f0c98d0c31233f0ad0cd43a63310b88ca42843150900c501ea04f069810c13603505900a413401d042804c05a0080e949403a2f4f0e83d1039ec4f0e7310c39ac390e630e03969430e524dc39292c0e0193c35a6430c918dc3106330b818ac28262108f988021c34f07a0d0c1a43370588cac10831f0160c5039155c0de3d6438ef4d0e33d1034ac590e2b134388c380b0996438664d0e1190c3826370e018803583430c88cdc3203360aa8c7c28031509f8c501040590df815c21804d079810c1a203704c807c0ea01302e003c08c009015802037d55c0dec96c37925a0ddc9443752500dcb16c370c4f0d1b13436ec410db30e036a94f0bca5343689370d9a4b036465b0d8993c2be64d0d8190435e6370d718ac35a6200d60d6c31e3370c70cd82de32b0aa0c7c27c31509e8c5021605b0d5813c10004d0d5012c1de04106800dc16002b04c007c0e801302d803c08a009015002035355c0d4496c34f2500d33d6c34af5a0d23d3c346f4e0d13d24342f450d03d1033ec5b0cf313833ac380ce253c3369430bc25043349370cca4b033065b0cb993c32c6430ae990432a6370ca18d432662b0c9188032235b0c80d6831e34f0c70d3830e3310b70cac2a631f09e0c54276314085016c1dc04f0c6810c0fc0410c600fc19803706580d415e02b04b807c0e601302d003c088009014802031755c0c530e03129370c424b030e6410b698dc2a462b09d188030c35a0c28d6030834c0c18cd83043340c08ca830032805700dc12c02b039007c2fe0110bf004008600901400202fb2500be3d3c2f6f450bd3d102f2c4e0bc31082eec3f0bb30e02ea94e0ba25082e664f0b9190c2b46350b898a42e06200b78d3c2dc3430b68cfc2a231f09c8c54270314076813c19404303d80d4158029038804c0e001101380202d955c0b5c96c2d52500b4bd6c2d0f4f0b3bd142ccf440b2b13c2c8c430b1b0e02c495b0b0a5682c094f0afa5382bc9430aea5082b893f0ada4dc2b49360aca4b42b092c0ab99382ac6420aa8d6c2a834f0a98d0c2a433f0a88cdc26e31509b0c5021205b076013c19204305580dc2a002b03c80a412a01d037804c0dc011013002029f55c0a7496c29b2500a63d6c296f4f0a53d14292f440a4313c28ec430a330e028a95b0a2253c2869430a124dc28292c0a0196c27e65a09f193c27a64e09e190c27664209d18f827263709c18d826e62b09b18a821035b0758d3c1903430600cfc15433704a0cac0da31f0360c740b23190210c5404a31409a816826804e099810826403f09880d826002a097804825c00f096c940258f4f095bd10254c4f094b10c250c39093b0e024c943092a4dc24892c091993c24464309098dc24062b08f988020e34f0750d0c18e33705f8ccc15232b0498c7c0823150120c5023c04f08e810c23803708d80cc23402b08c807c23001308b803c22c00908ad570208f5908a3d34226f440723164224c3804f196422264d088190c21e63708718801043590868d5421834d0858d0c2143370848c7c2103150838c501d204306300dc18a036035804c080008083557020b25b08249682072510814940202f5a080316c1fec4f07131341fcc3807ea53c16e94d07e25041f693707d24b01f265b07c193c13a64d07b99041ec63707a98ac1e86200798d6c1e434f0400d341e234b0780d241de3410770cdc1da32b0760c7c1d63150750c501d205b06200dc18603605400ac0d4013034804807e00807455701cf25b07349401caf5b0723d681c6f4f0713d381c2f450703d101bec5b06f30e01ba94f06e250c16c94106da4dc1b493506ca4b01b065b06b993c1ac64304e19041aa63706a18d41a662b06918801a235b0680d3c19e34303f0d0419c33f0668cf41983370658cd419432b0648c7c1903150638c5018c05b062816818804f061813814e02b034004c0ce01201f002018555c060b0e018062105f988017c05a05e80d817801e05dc940174f4f05cbd14170f4405bb13816cc4205ab0e016864f059990c13663505918a41626200580d3c15e3430570cfc0f63350568cc41583290558c7c1543150548c5015004f053810c0cc01301e802014d55c052c96c149250051bd6c144f4f050bd14140f4404fb0e013c95a04ea53813894204da4d813463604c8d6c13034f04b8d0c12c33f03c8ca412a31d04a0c54126314032804812555c048c96c121250047bd6c11cf4f046bd14118f44045b13c114c43044b0e011095b043a53c10c943042a4dc10892c041996c10465a040993c10064e03f990c0fc64203e98fc0f863703d98d80f462b03c98a80f062503b98840ec62003a8d6c0e834f0398d0c0e433f0388cdc0e03360378cac0dc32a0368c540d8314035816c0d404f03481380d004303381080cc03703280a80b000e01e00200c955c031c96c0c5250030bd6c0c0f4f02fbd140bcf4402eb0e00b865b02d993c0b464302c98800b031e02b81680ac05802a81380a804c02981080a404002880d80a003402780a009d55c026c96c099250025bd6c094f4f024bd14090f44023b0e008c65b022993c08864302198fc084621020988008035a01f8d3807c34201e8cd807831e01d806807525001cbd3c070f4401bb13c06cc4301ab0e4068c38019a50c064937018a4b006064f017990c05c63701698ac0586200158d3c0543430148cdc0503330138cac04c31f0128c5404831401180cc04400f010c940040f4f00fbd1003cc4f00eb10c038c3900db0e003494300ca4dc03092c00b993c02c64300a98dc02862b009988002434f0088d0c0203370078ccc01c32b0068c7c0183150058c5001404f004810c01003700380cc00c02b002807c008013001803c004009000802000007f 19 6 13 12 1 7)⟩
def c1Bounds : List Bound := [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N0 : treeBlock 0 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N48 : treeBlock 48 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N96 : treeBlock 96 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N144 : treeBlock 144 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N192 : treeBlock 192 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N240 : treeBlock 240 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N288 : treeBlock 288 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N336 : treeBlock 336 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N384 : treeBlock 384 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N432 : treeBlock 432 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N480 : treeBlock 480 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N528 : treeBlock 528 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N576 : treeBlock 576 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N624 : treeBlock 624 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N672 : treeBlock 672 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N720 : treeBlock 720 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N768 : treeBlock 768 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N816 : treeBlock 816 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N864 : treeBlock 864 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N912 : treeBlock 912 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N960 : treeBlock 960 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1008 : treeBlock 1008 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1056 : treeBlock 1056 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1104 : treeBlock 1104 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1152 : treeBlock 1152 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1200 : treeBlock 1200 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1248 : treeBlock 1248 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1296 : treeBlock 1296 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1344 : treeBlock 1344 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1392 : treeBlock 1392 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1440 : treeBlock 1440 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1488 : treeBlock 1488 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1536 : treeBlock 1536 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1584 : treeBlock 1584 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1632 : treeBlock 1632 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1680 : treeBlock 1680 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1728 : treeBlock 1728 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1776 : treeBlock 1776 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1824 : treeBlock 1824 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1872 : treeBlock 1872 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1920 : treeBlock 1920 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N1968 : treeBlock 1968 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N2016 : treeBlock 2016 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N2064 : treeBlock 2064 48 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1N2112 : treeBlock 2112 17 (caseNode c1 c1Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B0n96 : treeBlock 0 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 0 48 48 (caseNode c1 c1Bounds) c1N0 c1N48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B96n96 : treeBlock 96 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 96 48 48 (caseNode c1 c1Bounds) c1N96 c1N144
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B192n96 : treeBlock 192 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 192 48 48 (caseNode c1 c1Bounds) c1N192 c1N240
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B288n96 : treeBlock 288 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 288 48 48 (caseNode c1 c1Bounds) c1N288 c1N336
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B384n96 : treeBlock 384 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 384 48 48 (caseNode c1 c1Bounds) c1N384 c1N432
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B480n96 : treeBlock 480 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 480 48 48 (caseNode c1 c1Bounds) c1N480 c1N528
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B576n96 : treeBlock 576 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 576 48 48 (caseNode c1 c1Bounds) c1N576 c1N624
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B672n96 : treeBlock 672 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 672 48 48 (caseNode c1 c1Bounds) c1N672 c1N720
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B768n96 : treeBlock 768 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 768 48 48 (caseNode c1 c1Bounds) c1N768 c1N816
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B864n96 : treeBlock 864 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 864 48 48 (caseNode c1 c1Bounds) c1N864 c1N912
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B960n96 : treeBlock 960 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 960 48 48 (caseNode c1 c1Bounds) c1N960 c1N1008
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1056n96 : treeBlock 1056 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1056 48 48 (caseNode c1 c1Bounds) c1N1056 c1N1104
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1152n96 : treeBlock 1152 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1152 48 48 (caseNode c1 c1Bounds) c1N1152 c1N1200
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1248n96 : treeBlock 1248 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1248 48 48 (caseNode c1 c1Bounds) c1N1248 c1N1296
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1344n96 : treeBlock 1344 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1344 48 48 (caseNode c1 c1Bounds) c1N1344 c1N1392
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1440n96 : treeBlock 1440 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1440 48 48 (caseNode c1 c1Bounds) c1N1440 c1N1488
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1536n96 : treeBlock 1536 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1536 48 48 (caseNode c1 c1Bounds) c1N1536 c1N1584
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1632n96 : treeBlock 1632 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1632 48 48 (caseNode c1 c1Bounds) c1N1632 c1N1680
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1728n96 : treeBlock 1728 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1728 48 48 (caseNode c1 c1Bounds) c1N1728 c1N1776
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1824n96 : treeBlock 1824 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1824 48 48 (caseNode c1 c1Bounds) c1N1824 c1N1872
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1920n96 : treeBlock 1920 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1920 48 48 (caseNode c1 c1Bounds) c1N1920 c1N1968
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B2016n96 : treeBlock 2016 96 (caseNode c1 c1Bounds)=true := @treeBlock_merge 2016 48 48 (caseNode c1 c1Bounds) c1N2016 c1N2064
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B0n192 : treeBlock 0 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 0 96 96 (caseNode c1 c1Bounds) c1B0n96 c1B96n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B192n192 : treeBlock 192 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 192 96 96 (caseNode c1 c1Bounds) c1B192n96 c1B288n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B384n192 : treeBlock 384 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 384 96 96 (caseNode c1 c1Bounds) c1B384n96 c1B480n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B576n192 : treeBlock 576 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 576 96 96 (caseNode c1 c1Bounds) c1B576n96 c1B672n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B768n192 : treeBlock 768 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 768 96 96 (caseNode c1 c1Bounds) c1B768n96 c1B864n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B960n192 : treeBlock 960 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 960 96 96 (caseNode c1 c1Bounds) c1B960n96 c1B1056n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1152n192 : treeBlock 1152 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1152 96 96 (caseNode c1 c1Bounds) c1B1152n96 c1B1248n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1344n192 : treeBlock 1344 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1344 96 96 (caseNode c1 c1Bounds) c1B1344n96 c1B1440n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1536n192 : treeBlock 1536 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1536 96 96 (caseNode c1 c1Bounds) c1B1536n96 c1B1632n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1728n192 : treeBlock 1728 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1728 96 96 (caseNode c1 c1Bounds) c1B1728n96 c1B1824n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1920n192 : treeBlock 1920 192 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1920 96 96 (caseNode c1 c1Bounds) c1B1920n96 c1B2016n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B0n384 : treeBlock 0 384 (caseNode c1 c1Bounds)=true := @treeBlock_merge 0 192 192 (caseNode c1 c1Bounds) c1B0n192 c1B192n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B384n384 : treeBlock 384 384 (caseNode c1 c1Bounds)=true := @treeBlock_merge 384 192 192 (caseNode c1 c1Bounds) c1B384n192 c1B576n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B768n384 : treeBlock 768 384 (caseNode c1 c1Bounds)=true := @treeBlock_merge 768 192 192 (caseNode c1 c1Bounds) c1B768n192 c1B960n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1152n384 : treeBlock 1152 384 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1152 192 192 (caseNode c1 c1Bounds) c1B1152n192 c1B1344n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1536n384 : treeBlock 1536 384 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1536 192 192 (caseNode c1 c1Bounds) c1B1536n192 c1B1728n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1920n209 : treeBlock 1920 209 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1920 192 17 (caseNode c1 c1Bounds) c1B1920n192 c1N2112
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B0n768 : treeBlock 0 768 (caseNode c1 c1Bounds)=true := @treeBlock_merge 0 384 384 (caseNode c1 c1Bounds) c1B0n384 c1B384n384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B768n768 : treeBlock 768 768 (caseNode c1 c1Bounds)=true := @treeBlock_merge 768 384 384 (caseNode c1 c1Bounds) c1B768n384 c1B1152n384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B1536n593 : treeBlock 1536 593 (caseNode c1 c1Bounds)=true := @treeBlock_merge 1536 384 209 (caseNode c1 c1Bounds) c1B1536n384 c1B1920n209
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B0n1536 : treeBlock 0 1536 (caseNode c1 c1Bounds)=true := @treeBlock_merge 0 768 768 (caseNode c1 c1Bounds) c1B0n768 c1B768n768
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1B0n2129 : treeBlock 0 2129 (caseNode c1 c1Bounds)=true := @treeBlock_merge 0 1536 593 (caseNode c1 c1Bounds) c1B0n1536 c1B1536n593
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1Proof : Holds (caseBound c1) := caseSound c1 c1Bounds (extendKnown (bound:=r1) (extendKnown (bound:=r2) (extendKnown (bound:=r3) (extendKnown (bound:=r4) (extendKnown (bound:=r5) (extendKnown (bound:=r6) (extendKnown (bound:=r7) (extendKnown (bound:=r8) (extendKnown (bound:=r9) (extendKnown (bound:=r10) (extendKnown (bound:=r11) (extendKnown (bound:=r12) (extendKnown (bound:=r13) (extendKnown (bound:=r14) (extendKnown (bound:=r15) (extendKnown (bound:=r16) (extendKnown (bound:=r17) (extendKnown (bound:=r18) (extendKnown (bound:=r19) (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) r19p) r18p) r17p) r16p) r15p) r14p) r13p) r12p) r11p) r10p) r9p) r8p) r7p) r6p) r5p) r4p) r3p) r2p) r1p) (by decide +kernel) (by decide +kernel) c1B0n2129
def c2 : FiniteCase := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,[0, 1, 3, 4, 5, 6],9,59,[1538, 263681, 528897, 795137, 1065986, 1344514],⟨[3, 9, 17, 24, 34, 66, 96, 123, 27, 43, 51, 57, 10, 18, 33, 40, 48, 65, 72, 80, 0, 1, 2, 8],rfl⟩,(0x82031080c00030910814420508842601402424030500c1409281c0a05828148a051241a09058241289049209848251209248243201808042181c06038180c86031141a05038140a85029109844231108a4422310180402209148243209068241308060201105128142a05068140b0406010090110804220100c0211008240203,57),0x687fff111410400c2222fffd0410001e887a21f9420094f213c82bf0bf3110a442f9e73c3c47c11f0514f,0x2007ffe00000000860000fffc0000109e007801f80006b0f003c003f0073800000079e7184003c00f00007,(decodeNode 6 19 0xf44b187163d1177a22cc3859e88ab0e154962a92c44c408bd10e92816f4429886530e0a4961492c24c404a4b08310112501de883c94067a20cc381525829880501a08028124a01bd1031a7063420c63c1bd10262184c38092581188021a1843370862a10c50200784943052580990c131b8262b04c400810c101b8202b0403e0804c10078200904010080fc0),graphMoves,(dagLookupLinks 0xfe0fe0fe0fe0fe0fe0fe0fe0fe0fe0f64f60ee4ee0e64de4de0de0de0de0de0de0de0de0de0de0de0de0de0de0de0de0de0de0d64d60ce4c64be4be0be0be0b64b60b609ec9e09e098380c7a37436e36835a752446632a038001 0xf4f4474c38ee92c6e620f2f4474c38ec92c6a620f2f4472c38e892c6862074f4472c38f092c6662070f446ec386a92ce462070f446cc386892ce26206ef446cc386692c646206af4468c386692c62620e4f44e2c386492c6262060f44dec43dcc385692ccc643c8637ba621b062054343503374431f2a3145f250daf44ae3145cf445ac4358c385692cca643c6637b8621ac620523434e3374231f283145492c52620360085092c4e620340084d2504af44a63144925046f44a4314c5250c2f4444c384292c40620b231432008be04cbc0403e0343c0283b25038f44a26203634e343423231e30f442ec432cc382a92c28620263432433722315203141e00f9af4494c4392c381c943989371a92c18643166371462b126208c3438a3379032b8e31f8431582314100430e0370c02b0a01f080130600f04009020080003f 12 5 13 6 1 6)⟩
def c2Bounds : List Bound := [r21,r22,r23,r24,r14,r25,r26,r27,r28,r17,r29,r30]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2N0 : treeBlock 0 48 (caseNode c2 c2Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2N48 : treeBlock 48 11 (caseNode c2 c2Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2B0n59 : treeBlock 0 59 (caseNode c2 c2Bounds)=true := @treeBlock_merge 0 48 11 (caseNode c2 c2Bounds) c2N0 c2N48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2Proof : Holds (caseBound c2) := caseSound c2 c2Bounds (extendKnown (bound:=r21) (extendKnown (bound:=r22) (extendKnown (bound:=r23) (extendKnown (bound:=r24) (extendKnown (bound:=r14) (extendKnown (bound:=r25) (extendKnown (bound:=r26) (extendKnown (bound:=r27) (extendKnown (bound:=r28) (extendKnown (bound:=r17) (extendKnown (bound:=r29) (extendKnown (bound:=r30) (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) r30p) r29p) r17p) r28p) r27p) r26p) r25p) r14p) r24p) r23p) r22p) r21p) (by decide +kernel) (by decide +kernel) c2B0n59
def r31 : Bound := projectFact 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f [0, 1, 3, 4, 5, 6] 10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r31p : Holds r31 := c2Proof
def c3 : FiniteCase := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,[0, 1, 3, 4, 5, 6, 7],11,497,[1538, 263681, 528897, 795137, 1065986, 1344514, 1642504],⟨[3, 9, 17, 24, 34, 66, 96, 136, 160, 251, 27, 43, 10, 33, 40, 48, 72, 146, 193, 208, 0, 1, 2, 8],rfl⟩,(0x901818180a0601406090602804490421804424110008802290082c421128060601818088502240a80900960b20821120824420920908826040a2042224128180a00908882031080c14180906004230002400030910814420508920881098050090900c140305025a0f068361a0d26834582e160b4582c960b0d80e06032180c24934924b2492692493482c120984824504c241289048a4120d02a140a45028940a0d00a040220a07028160a0522814490c8241a09058241289049209848251209248243201808042182c06070180e06032180c450a8141a05038140a8502910a844261108c442291088c40a010180402209148243209068241308060201105228144a050a8141a0502c10880406010090110804220100c0211008240203,127),0xa0b00107ffffff84008421008401a8004600190fff0200fffe8421408103430e05e10a11112245088bffff40810958e0800c003d07f043c887c841f8909206c6c81a14a122444a7c827c40aff080946049cbc6213e3c4210a2104f9f1c82dc17019c1e3e048f821f021f81424f,0xa0b00107ffffff80000000000002b810f628000ffe0000fffe0000000002885c110803000000000003ffff00000658700044493c07f003c007c001f800134014001065800000007c007c000ff00020000539c7001e3c00000000079f1c001c2ff180201e0007800f000f800007,(decodeNode 9 22 0xb1b97a26c9871ad61c6ad8b19e7a2605871817a25e98717a7a25c5871717a25ac6b1687a25806b15d1a65746b1571a655de89531ac54069950008541e894e61c5398713261c4c18712d7a2419e88f87a23dd870f70243c8098ef4a03a9258e6310399258e5310395e88d47a2339870ce496339ea8bd02c2ee4a0b99282de4a0b69282d64a0b09282b24a0aa61c2aa4a0a992829e4a0a67a729801ea561c2924a0a361c28de88a2621a89872a261c28a4a0a1027284054a17a22800b0a0021280068a092827de889f02727c0849f01527dea89b9282698709a7aa25e4a09461c2512589462a24e4a08c7a7231e888c61c231ea88b928219e9c867a221987086496219890854a4210c408218a20a4a0803101fe4a07e4961f64a0799281d9e88769281d5e88759281cde88739281be4a06e7a21b80606e9281ade886b9281a9e886a9281a5e886901a1a64a0687a21a24a0677a219e4a0647a21924a0617a2184650619281740385a7a21658865961c965870591a196466e59199965e885761c15de885561c155e88546219518725461c1506865419b9506665492814de885331014c69c531a114c67c537a21498865261c949870521a194866e5219994862a5218a14a4a05032a13cc904e3141340504d928129e884a61c12a4a0487a21224a0467a21192684561c10d25843496104c404118a104054414960fcc403f1988fc6283f0150fc03c3f7a20f64a03c3100f18703b3100ede883a61c0e4c40399280d64a0347a20d0cc83132c0c4638310060c18702f3100bc6822f9280b9e9c2e61c0b8c402e19a8ba4a02d7a20b64a02c7a20b12582c3270b0c842c18a0b24a02a0248aa4a0297a70a401c297a20a004e2800d8a001e2861c09e4a02661c099e88256218958722561c0958702492808d87023928088c9c2218e88a4a0217a20864a0207a2081e881f62187d8721f61c07d2581f6208798701e496078c401e928075e9c1d7a4875e881d6270758701d496074c401d1a707407a1d61c0712581c1ac0706981c19a0706501c92806de881b928069e881a7a2064684197a206187018496060c841831b060c54180070612861749605cc861731b85cc661731585cc421731005c01e1792805925816320858c401602705803c16928055e8815310055e8814496050084147a204a4a0114a084526e11496045e88104a7841258103270418700f31b03c03a0f928039e9e0e6270398840e61c03a4a00d7a7835e8a0d61c03529c0d4a103526c0d7a20318860c61c8318700c4a183126e0c4960300660c00d83001e0c92802d8700b4a082d26e0b49602cc960b32082cc6e0b31582cc420b31002c6560b928029e9c0a7a20298700a4a782926a0a496028c9e0a31f828c6a0a315828c420a3100286560a18f82809e0a02702a4a00949602409c0901502403c09928021e9e087a2821e880862702188408314820c40081a78206520892801de9e077a281de880761c01d29c074a101d26c0749881d2580731b01cc40071a781c6860718e81c09e0702181c06c07928019e9e067a2819e8806327818c860631f8180b006027018098060210180800601a01803c0600e01989e0561c01529e054a181527e0549b81525a05496014c6e0531b014c5605315014c4e05310814c400502781409c05021814084050158152580402c010068040150100500492800de9e037a280de880349600cc9e0332180cc7e0331080c69c031a100c6540318f00de88026218098720261c0092860249b80925802321808c6e02319808c5602310808c40021a180866e021998086560218f8086360218a808628020198080360200780928601496004c860131b804c6601315804c42013100040860101b8040660101580403e0100d80402601007804012010040040fe00),graphMoves,(dagLookupLinks 0x23a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e80474023a011d008e804740239831cc08e604730238071c008e0046d0e36811b408da046b0a35031a808d20c690234811a408d204690234811a408d204690234811a408d204680634011a008d004680234011a008d004680234011a008d004680234011a008d004680234011a008d0046706330319808cc046602330119808ca0c6406308718408c2046102308118018be0c5c0e2d8316818b4045a022d0116808b20c58062a8714838a20c4f0a278113c089a144d0226811283894044a02250112808901448022401118288c044602218710c0886044302218110c08801c3e0a1f010f80878143c021e010e4387204370a1b810dc086e0437021b810dc086e0437021b810dc086e0437021b810dc086e0437021b810dc086e0437021b810dc086e0437021b810d0386804330619030c4186204300617830bc085e042f0217810bc085e042f0217810bc085e042f0217810bc085e042f0217810bc085e042f0217810bc085e042f0217810bc085e042f0217810b03858042c0216010b00858042c0214870a4085204260e1301098084c0426021301098084c042602130109808461c23021181080383a1c1c060e010700838041b060d8106c08340c19060c8106408320418060c01058282814120a080504008200410020801040082004100208010400820041002080104008200410020801034381a040d020681034081a040a0e05010280814040a0205010280814040a0205010280814040a020500ff4d7fa03fd01fe02fe827f20bf901fb06fd807e423f009f608f8c97c603e301f180f8037b043d801eb82f5037a413cf0de606ef4f7684bac21cd24e60272a1b8835c208e0046f4337809ba86dd406e80b6b25b580dac06d40b6a01b500d80a6bc135b0dac06d5436a41b5201a900d20a68e0b4701a380d1c068e033c2d9d04ce026700336099a04cc0465e0b2d099602c9086480324018e10c7006380318118a86c5406241b06318300c1805f462f6117b00bd805e61af00d7608ba045ca1ae5017280b8835c402e2016f08b5c75a81ad10d650eb1c35881abd1d5a12ad005621ab1015706a94953c3a95254a80a3095160a8a054386a1c050e027d293e809e834f20a760d3a049d004d4526a01328a99404be325f012c8c95834a8125305288492c64940a4905218c8f464761239091b068d0245c3226211186870741a7a0424fd927a523ce11e40ced1476023aa19d110e70672c337e61b918d69869c634819a10ccf84660730c918018be865e832d4815554a1a44c1324e4912547fa639d819cc8b468570c275110ac0744427ca118907070206000be0001 0x7c00b0f7bd13d561c3a692c7bde89ea30e1d24963dc3587b4680f730e1ed61c3d8c5879c650f30ca1eb19e3d433c7ade88f530e3d13103d23407a0680f4bd11e861c7a031479c668f30cd1e731a3cc63479de88f330e3cf0043ca65878cc98ef18d1e432c3caf44f38c40f2bd13cd3103c8358f88699f00041e37a279862078de89e59881e21ac3c234cf7c020f00d61df1a63b6010779e88ed1881de7a23b26207746b0ee0d31db0083b4f44765870ec1963d73263ae640761870eba4b1d761c3ac92c759870eabd11d461c78e92c755e88e9b0e1ca4963aaf44749871e4a4b1d47a23a6c38725258ea3d11d261c39092c74de88e930e1c749639e334744090e80131cf1a039e940738cb0e61931cd32c39664c739258e69881cc496396620729e89e4b0e1c7496392f44721870e3a4b3bf7a2f68f44711886e1b0fdbf61cb68c38e09287ce24df08496338643608c6ea618ad0831038cf54ed9871851881c502c389250ef9871819881c392878494ef04c53809881c29286003147064a0a48ca6ff18a290012ece4a0e03d11bc496736641c1cc40bf8d058919aaf03293f8628e04943bb7a2628620eca4a0dfbd11be627378c42e6526b8324b17631a9f86206f5898dfc943ba7a262492ced5871849881be92837ac38c08c40de4943b97a26226206e9e8bd8bd11b6621b68c38e05287d124df0549632e643638c7ec398dd47315a546213e8c40d80cfda918db772506e5870d9a4b37e326f10641ddcc6b7e9881961a69f23146ea4a0dcbd39b5620b64c38dd52837da4b1943209f0620ec5e88dbb10db161c70c943e7d26f94a4b6f749633e643618c6ea318ad33313a526213dcc40d68c9da818df50027eb4036dc003db761c6166206da4a0dab0e304310368f446cd886d930e5b161c714943e0d26fb7a4cf2b496e1e92c678c86c998dd453159ec6206c24a18724b1af02735c02a6b5e88d60161ab0213540346a64a0d43d130d49634e04e698084d280a9a361c34092c689870cfa4b12418a348f5468e4a0cdb135a261c33c92cd10c9bc29906e13103203364f463cd0bd51a092832cc4d67d870cf24b343326f08641b80c40c78cd93c18f2463146758a89d00419c61c32e92c484628cda4b196310240008669870caa4b11018a332c386512588f8c519c928336f4e669e88ccb0e193496684641dd0c6b6f9881901a727231e661ea8cbc941967a732af44651870c9a4b341320ee6635b78c40c78d393818f23c3146498909a8041914a4268010640c40c78c518e61c31833663a4a16ea4b18d1a731632a634c40c64942dc18a31692c62a4a0bfa5058949ab0e92c510c82c298d6f33102e432a62a4a0bf25058849ab0c92c50cc82c218d6f23102e232a6264a0c43d12f518a2e001c61e4a0c33d12f431030b250611e89910c5183928304f445fd884beb0f57b61c2f09425d9258a118d574314dd66205c86848e0c5183928302f445f9884be30f57a61c2ee9425d5258a098d573314dd46205c46848d8c5182928302f44bc4c40c000c17f9282fcf44bc0628bec9417c7a25de3145ee4a0bd3d12ee3102f20345e24a0bbbd12ed18a2e00285da4a0babd12ec3102e92505cde898e8c51729282e2f445c06517480216f9285ce92c5b46b0b20d31621a02b632a554650b601916101a2a801c5ac6c8b00d01531942df250b99258b50d61651a62be340568654a90ca1690322bc034560038b401915d01a2ae01cd9ccc9ae19635618e2ce064570080ab00a16e00e2daf445b1886b5b0e56a61c2d23435a066eb38ccf2818adca314599e88b2b0e2e318a2c8f4458d871710c51627a22c2c43581872afb0e15e1a1aba337570667938c56e418a2b7250569e88ac9881581a72ae34255867d930c51557a22a8c4354d872a930e1511a1aa033753c666a70c554d18a299250d1de88a2b0e3444a76849424fd2598d18813d1a727234252cca8a5192149314690328520050a3c941467a228ac38d0d29da0a5093e4966326204f069c9c0d091818a28925050de898b8c5140312285250505e898b0c514049a66e334cfe4a19f3d113f61c27c92ccecc6d9b18aad531027634e4d86846a8c513d4962786204ec6289d00ab3500f27292c4e0c409b8cc53618a26a02a4d003c99bd11311ac66034ccb8685968d012f19a265250cc58709898813061c25e6204b9e8896b0e12c3102572504a98716d24b121327238636468c54900d611f3262572504a58716ca4b124327236636464c54954941297a25b692c48cc9c8f19091831522e3584886988b0d311d1a025066449ccb0930c711531424a00c48189a9230e12331022e34d4886836b8c5121928240f4e441e888fb0e11e31022c34147466b6b0c511c928236f44b606288d4941197a223092c45cc9c8b1908d531022a314449e8a87bd110a621a10c3840d28680a4fcfe49b9f892d3e925878990ce131b9be62bb4cc40658cfcc5193a2925044587083a4b0f93101e034d3d4682768cd6cf18a22604944a4a088bd3909620a0cc384092827c24b0ec320d9c62044001c87bd110b621a0ac384112867ea4dcfb4969ee92c3d0c867018dcde3159ba62736cc43669880c419398431b43804e86806d0c007a16c383506288549410961c5a4314421e8883b10d0661ca0ac383d925879990ceb31b9ce633368c426998810461c1a431440e4a08130e0d118a203250400c9c7f8c74d018a1fd2503f5e88678c50fc9281f6f44338c407d3d10f96219f0c393dd8707b24b0f23219d4637398c666c9884cd310194333304636783134f56209e8c383cd258791880e919b1e32503c1e9c77bd24ee7a21dac4e3b187075a4b0ea3101d234e3606287400f4c90189cec38399258728d60e41a61c633438865070c940e07a21ae31437e4a06f3d10d618a1baf443706846dbd10da61c1b292c360c846b98d8d63151aa00eb4de8967b10ece61cd9ac383512876924dcd34961a4643344c6e6818cccf31599c621334c40640cccc318dd86033b2003666003ccb92819492c324c82641880c702718c01e3164a0623d10c3310184f4430525860010ab1626d46c38af526c589934bd32097263728cc413b8d369b194d1a31f8986283b81349b02091a037140026130020bf7a2566c43ab987353b0e0bb4a19709372d926655a4b4a14964f66439c4c6f2f98ce91315d006278dcc43151880991a19163371b4656278c7c2418a17d250ac189b5130e0b14a697a9412f126e5da4b0b731b1546209d869b4d0cae8c18ec4a3141b009a4b81048a01b89c01308c0115c4942b07a7174f44aa58705ca53cb04a0d6e9352e12585b9938a93104d6341a58657440c762218a12c04f1ac0824400d44d009844008ada4a05b30e2b532716a636ad063b108c50b400e89801308401059c940b27a7d5af45a99e8858b138b062115ec382a0c413d0d3e701a1cbc33fa4066b1b0c562918a12a04f21c0863500d4750148ce01d12c026100020ae92815af4f2b1e8b52bd10ab61c15494e2a52845424da79327cde643974c7f4718a635310c5062025069e430d0c6619489431f07c62853bd10a662194ac3929187051a50ca249b94292c9e0c873718de5c319d3862b8d0c43139880931a190a3371fc6663a0cac4918f87831b0cc62a0f0c50a001993e01b27801e4ec94090626938c381dd29a4da5049a49b93292c1b0c9a4c192c9732092c637254c564a18849331048e34d9c8682490cae8418fc3431420806e4080d86200f88201310002417002091928120f4e23de884730e08d4a78ec94123126a45a4b08a3278d6641224c7e4418d48731590c621214c41228d066319a90832b20c63f0c8c508202790204e18403e1f804c3e00905a0082024a03fa4b2183100fc04e1f40543e00787b9280f4f4f1e5e8a3c3d10776270ecc421a8c6a3a98a4743100e634f9946872d8cfc4719a8e43298c862b0e8c506000f0e32501c1e9e37bd146e7a20dac381b129c35a5086a49b0d29311a12583398d8663100ca34f1906872d0cfc451948c631d8c462b0e0c50620278c204318006c1e804c2c0040bf250179e9e2ebd145c7a20b664f168c862c98fe30310c366201600b02b8138560260aa0421500802980d05200f0a201c93e4a125bd3e4a7a2c92f4414189f27310c4f61c09c94f1352862624fc4b49b89492d12525924193e4732748c643914c852218fc4831b88e636118c562298a844313886621108c411e8d0e4119bc803368fc6571f0caa2b18a08204f10009c1f810c3e02107a02b0ac0111e3d103c4960760588e80991c810a380200740340e40541c00a03792806cf4f0d5e8a1a3d103349606464f0c4c861818fc2f310c2e6200b869c168d082c19505631e0a9e8814b10c2861c84ec3809928612a4dc24496046643088c6e1098cc2031583e621078c400e8d0c1c19b8363330686560c8c7c1818d82e3150586280a80cc1400d82600f845e8906b10e0c61cc16c380492870824dc1149602064303cc6e0718cc0d31581862102cc41038d0e0619bc0a333828657048c7e0818dc0431580462805010c0901b81003301c05603007c0500d80801300c01e0100240100400007f 17 6 13 9 1 7)⟩
def c3Bounds : List Bound := [r4,r31,r2,r32,r33,r34,r35,r36,r28,r25,r8,r37,r9,r21,r38,r24]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N0 : treeBlock 0 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N48 : treeBlock 48 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N96 : treeBlock 96 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N144 : treeBlock 144 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N192 : treeBlock 192 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N240 : treeBlock 240 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N288 : treeBlock 288 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N336 : treeBlock 336 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N384 : treeBlock 384 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N432 : treeBlock 432 48 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3N480 : treeBlock 480 17 (caseNode c3 c3Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B0n96 : treeBlock 0 96 (caseNode c3 c3Bounds)=true := @treeBlock_merge 0 48 48 (caseNode c3 c3Bounds) c3N0 c3N48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B96n96 : treeBlock 96 96 (caseNode c3 c3Bounds)=true := @treeBlock_merge 96 48 48 (caseNode c3 c3Bounds) c3N96 c3N144
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B192n96 : treeBlock 192 96 (caseNode c3 c3Bounds)=true := @treeBlock_merge 192 48 48 (caseNode c3 c3Bounds) c3N192 c3N240
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B288n96 : treeBlock 288 96 (caseNode c3 c3Bounds)=true := @treeBlock_merge 288 48 48 (caseNode c3 c3Bounds) c3N288 c3N336
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B384n96 : treeBlock 384 96 (caseNode c3 c3Bounds)=true := @treeBlock_merge 384 48 48 (caseNode c3 c3Bounds) c3N384 c3N432
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B0n192 : treeBlock 0 192 (caseNode c3 c3Bounds)=true := @treeBlock_merge 0 96 96 (caseNode c3 c3Bounds) c3B0n96 c3B96n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B192n192 : treeBlock 192 192 (caseNode c3 c3Bounds)=true := @treeBlock_merge 192 96 96 (caseNode c3 c3Bounds) c3B192n96 c3B288n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B384n113 : treeBlock 384 113 (caseNode c3 c3Bounds)=true := @treeBlock_merge 384 96 17 (caseNode c3 c3Bounds) c3B384n96 c3N480
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B0n384 : treeBlock 0 384 (caseNode c3 c3Bounds)=true := @treeBlock_merge 0 192 192 (caseNode c3 c3Bounds) c3B0n192 c3B192n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3B0n497 : treeBlock 0 497 (caseNode c3 c3Bounds)=true := @treeBlock_merge 0 384 113 (caseNode c3 c3Bounds) c3B0n384 c3B384n113
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3Proof : Holds (caseBound c3) := caseSound c3 c3Bounds (extendKnown (bound:=r4) (extendKnown (bound:=r31) (extendKnown (bound:=r2) (extendKnown (bound:=r32) (extendKnown (bound:=r33) (extendKnown (bound:=r34) (extendKnown (bound:=r35) (extendKnown (bound:=r36) (extendKnown (bound:=r28) (extendKnown (bound:=r25) (extendKnown (bound:=r8) (extendKnown (bound:=r37) (extendKnown (bound:=r9) (extendKnown (bound:=r21) (extendKnown (bound:=r38) (extendKnown (bound:=r24) (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) r24p) r38p) r21p) r9p) r37p) r8p) r25p) r28p) r36p) r35p) r34p) r33p) r32p) r2p) r31p) r4p) (by decide +kernel) (by decide +kernel) c3B0n497
def c4 : FiniteCase := ⟨0xffffffffffffffffffffffffffffffff,[0, 1, 2, 3, 4, 5, 6],11,399,[1538, 263681, 526849, 791041, 1057281, 1328130, 1606658],⟨[3, 5, 6, 9, 17, 24, 34, 66, 96, 127, 15, 23, 10, 18, 33, 44, 52, 65, 76, 84, 0, 1, 2, 4],rfl⟩,(0x2406060602818050182418060182201848060a018a0112a11460111a09490092611450091609482112082442090906082602090824111088888050908882031080c14180601804430108c00110002400030910814420508842601201424030500c14092a1d0a85c2a158a855281c0a05828148a051261b0985c26138984d241a090582412890492219088462211482612094482492091482432018080421a1d0683c1a0d86835181c06038180c86031161b0583c160b8582d141a05038140a85029121904826120944261108c442291089442231018040220a07028160a0542452090c8241a09058241308060201106070180e06034144a050a8141a05038140b040601009020180805011080422010180403008440209008140203,126),0x1a0881804343ffffff88889084010080680884a0830888890bffffff0802010251412411003fd1020ff44083ff848089405380420144ff04113fc1084bff0100eaa0108023c3c388f0f0e2388e2322038002bb9e622224148889055f17cbc401ffc567c3c4444fc11113f0852151f,0x2a9999940003ffffff00000000000000551990880180000003ffffff0000000193e02480213fc0000ff00003ff000009807800606300ff00003fc00003ff0000eaa0108023c3c380f0f0e0380e0300000009258e700000000000001f07c3c00001da6004000007c00001f0000000f,(decodeNode 9 22 0x1871464965198714349650cc814261c4f52593d61c4e92593a3204e4c69389284d5e89359284bde892f61c481259201944786511900843a4a1087a24224a1077a241e4a1057a2414629059283f5e88fd9283f1e88fc9283e9e88fa18a3ea4a0f79283d9e88f69283cde88f318a3cc050ee1a63ac650eb1ac39c650e7928355e88d592834de88d3928349e88d218a34a4a0d17a2344628d1928341e88d018a340098bb02c2dc050a592828e4a0a07a22800509e00f2100228100f20003c7eaae1e6ab8777a21d9870761a61d86807619a1d8650767b01d64a0729281c1e886f61c1bc6b06f1a01bc6686f1941bdea86e62a1b6ab8689281a006868aae1964a06561e196ab85e9281780805eaae16a4a05a49816aab856aae14e4a053aae1464a051aae13e4a04f01a139e884d61c1340524d0141340224d1b01318704b49612c6284b01b12c6a84a61c1252584918a12406c49015126ab846aae1164a045aae10e4a04331010eab8429281080b041928101e884061c1012584000990002240aae0fe4a03f02c0f80983e0200fa4a03d7a20f58703d4960f40263d0088f40803c01a0f18703b4960ecc403b0098ec0223baae0de4a037aae0da4a0360060cd870314960c46aa311a68c58702f4960bc6922f1a08beab82e9280baab82d9280b6ab82b9280ade882b61c0accb42b3270ac6282b00c8aeab82a9280a8c402a1ad0a86b02a1a70a86982a1a00a86682a1940aaab82792809eab82692809aab8259280940b425027094038247a208d8702300908c6aa201a487e4a01e7a20786aa1d1a48724a01b7a206eab81a61c0692581a02a86a4a01961c06525819024866ab818928062ab81792805eab816928059e881661c058cb416327058c841631b0580b41602705801c16627855870154a785528615496054026150078546aa1418a0506921318a04eab81292804867a1218a04aab8119280446621118a046ab81092804062810aae03e4a00f7a203d8700f31003c63c0f02d03c09c0f00403eab80e02a83a4a00daae0306aa0c02a8324a00b02482e4a00a7a202aab809626825870094a6825258091aa82466e099280218820861c021282084960206920819b82065608aae01e4a0077ad01de9c077a201c6b60719e81c66a0702d81c09e07aae01a4a00662d01989c0661c0186b6061a7818662061948180b606027819eb6057a20158b60562781587005321814c840531b814c6c05310814c400502d8140b40502781409c0502181406e057a20118700418f81063a040210100820402001006c0401a8100680401481005004004012ab80392800de880361c00ccb60332780cc42031ad80c6b4031a780c69c031a100c66c0318f80c63c0318d00c0b40302700c0840301b00c03c0300d80c03403928009e88026278098860261c00929e024a1809258021a78086860219b8086560218a808628020278080860201b8080560200980801e02627805870014a78052860149600409e0102180406e0101580402601007804012010040040fe00),graphMoves,(dagLookupLinks 0xd9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d9c0d942d8c2d803d800d800d704d6c1d6c0d6c0d642d5c2d503d500d500d404d3c1d381d341d301d243d240d240d240d201d1c1d103d100d100d100d100d100d100d100d100d100d100d100d0c1d081d080cf06cf00cec1cec0cec0cec0cec0ce81ce80ce80ce80ce80ce80cdc3cd03cc43cb83cac3c9c4c9c0c9c0c9c0c8c4c7c4c703c643c640c583c580c580c580c580c580c484c384c2c3c203c200c143c140c140c044bf44bf40bf40be83be80be80be80be80be41be40be40bdc2bdc0bdc0bdc0bd42bd40bd40bd40bd40bd40bd40bd40bd40bd40bd40bd40bd40bd40bc44bb44ba05ba00b943b940b883b7c3b703b643b640b640b640b640b640b640b640b640b640b640b640b640b640b640b601b5c1b5c0b5c0b581b541b501b500b500b500b4c1b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b4c0b481b480b402b400b400b382b380b341b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b340b2c2b146b140b0c2b042b040afc2ae46acc6ac42ac40aa87aa80a8c7a689a602a582a580a3c7a3c0a2079fc99f429ec29d859c459c409c409b449b409b019a049a009a0098c597859780978096849680968096419544954095409540928b928092808fcb8fc08f038f008e438e0189d189818845880186c586c086c0844a81ca80857f067e437d447b487a83798477887684740a7400718a6f0a6d476b876b026a82694569406787678065c765036443644061ca5f4a5f405f405e835dc35c855c415b83590a568a5602558253c7534252c251074fc54e854dc34d0349cd455244c244424344424441443f093c8a398c370a348a318c2cd328132410201016e510d80ad805d400560001 0xc719318c31a31a64c62cc68c730e18d4962ca008631870c5a4b17d008ac8008628c80c499618731a310658618c68c4b0e1884962c600861d870c324b17c008ac4008614c80c218d1831a030434060e4a0c13d135418a30234c600698c0c941807a26a63145fc668bf0cd37f9286fcf445fd870bf24b35218a2a40085f4650be0ca37332c2e664c5b0c81b91961783262d6640ddccb0bb99316a3202ec34c5bc680b48cd1751a62dc3405a0668ba0d016d19a2ce3285ec020bd3d117861c2ec31d574628bcbd117761c2ea31d570628bd4941797a26c26205e24a0bbbd13603102ed2505d5e88ba0c51737a22e2c385bc63aad0c51727a22e0c385b863aac8c51739282e4f44d7cc40b8c941707a26bc6205be4a0b73d116d18a2d9250dade89ab98836918f2d72505a9e89ab18836818f2d32505a1e88b38c51660142ca34c590650b18d61621942be658574c98ad19015731a2c0658570c98ac99015631a6b6658d60c98ad99015831a2aa6285864a0b03d135b18a2bf250579e89ac0c515d9282b8f4456c628ad4941597a22b031455e4a0ab3d115518a2a292cd41258a824b14f4962a804c54c0b0a900a1519286a0f445424a0a7bd114e01458462053403d78a4b6c049625462b448c4e789884c03102980112f80116098814b00f57a62052803d7824b6bf49625262b444c4e779884bc3105dc92daed2589418ad103139dc6212ecc40a4bd114861c29355cc9ccb2a3995733326d6462047063c760c5148aae64c659518cab991936b131023631e3ac628a3bd114661c662358514698a20d014319a28432847403a750021417b0232010501e889fb0e14092864a64d4f8c93969906b031022e31e3a06289fc94324326a7a649cb0c835798811618f1ce3144f9e889eb0e13c1ac65634c4ec6809d0cd13919423001d3980109c3d511400826ec5444c0209b494127326a66641ae4c40720c513592824c64d4c8c835c1880e318a26d55c4d64a15d18813401a2623404ceab89949413161e5d23144c1e889299052d31ad6a62038862897bd1124320a58635ad0c40708c5130aae25f250ad8c409701012b19a25b55c4b24a095a4c2e518a25555cca64a193a56b254a724492cb80c408e0d69171a761e31a37862861802129aae251250c992b5922539214965be62046c6b48b0d3b0e18d1ba31430c01093d571269285b8314496ab8924942db18a246034c8aab990c941227a2242c38c68c858a98daa431023435a45469d868c690d18c9483144800528f80a31e00ea3c01130c0108e8d811c61c23692c4686288c80db1401523035445d8708b24b11518a22803644c054895573119285b092cc3cc55860d6b091ac60634ebf86987e0d00f619a22355c4424a16ba4b30e31561635ac206b1810d3afd1a620c3403d4669828192fa02c20a04c3e80807980d10faae21d250434c40820100f901a1e4028432ab885c942d518a214058c040987f80d0f8014213250421e8883b0e1064965a8314414026820044d100420755c40a4a1698c510102c20004c3fc0807b80a0fe9281faf443f18707da4b2d218a1f40133e4022680022f802c5ee04c3e00807b80d2f69285eaf443d98707aa4b0f431059e3143cc027790048f200899e0083c64a077bd12ac4961c864e388c847018a8d831319c34e330684650ca8f09281dcf44aad258719938e13211be62a35cc4c668d38cb1a119232a3c6ab8784942ae4961d865a3a0c9c6f18a8c51931df55c3ba4a156a4b0eb32d1ce64e374c54620c98dc1b21d235836c6b0728d30da3141ac624a14650428070ed0061d8c383ad2586e0d64ea1aa9d234daa0628640048e861c1ce92c36c69a730d24e51a0d4e31431c024725570e392855431438aab870c942a918a1c155c37e4a06f3d10dd61c1b865a36cc9c521880da18a1b201930c0106c5570d79281ac6203546b46a0d60d31a71a434c344680680cd0cf19419d55c3364a1530c50ccaae197250a94628655570c992850a3143200b4638138c600e18af44311870618048c07a2178c382c8c865818dcae310d446202606864a0cdc9018f91a31b2fde885db0e0b132195e6372b4c434f9880971a192633723c63e460c6cc21aa946314304693508c50c092817ef442e4c9e5a990cac31094462022c6365f0d54a118a17a3492806285e4940bb7a217064f2d0c865598849f31011431b2eaab85cb0e0b84961543142dc0aa5b4940b561c16892c2a4628598124b2aae1632502a0628585570af92814e3142baab856c940ac7a2156c382a8cb4549938a832114e63623863a448c64a602d14a04e29001d5149429f7a2146c4fa858865130e0a14a794094327d2584d8d3c991a192a3372446574a813e91021d36037a640564f004c9d00793835526c6284d0d249918a13155c25e4a04b0cf49518a12955c24e4a0490cc49118a12155c23e4a0470c508800711b55c2324a045bd108a61c11262022063c4381688602710a008212ab9348d66831aacf233587c6283481648302a8f204d1580260f8020829284f8f449acc9f30990e38310c426201e069e388d0c5518f88a31b0d862a0e8c5081aae4d03592006ab390ca61e18a0be0591fc0aa3b8134540098380081fa4a12f0d367d1a4ce032986c6282f01347d0248e004114c0260d80207c9280f6f449a8c9f30190e37310c406201d869e378d0c5218f88831b0d462a0d0c507aaae0d2c591e589a3c30e05f4ac8ee94d1d9259280d64751aacc834d1d066f368cae1718a0c603716005625804c4a0090620090c001039c940686268e4c411c58702f2534704a08de92c93869a370d26591a08da3371b06570b0c506201b8ae02b1240262400482f00485c0081aeab8354940697ad0d0f4e19de88330d6e5c1a78a034119467a320cd63418ac3231418c0b631013c4700985a008186ab83049405f62d0bcc4e1758702e0d6c5b1a789c3351686622c8ca63318ac303141600b62b813c46009858008956ab9294940567adca8f4f155e882a316c536278a4c38944cb728196a4f327c9c64e144c862819084f31b89c636134c42261882471adc8c34f92c687250d0a4919bc903368ac62b150c504b02d89405a12409e2401384702188c03710c01f210038420068560090a801122d5724492808af441118711498804318fc8431e10863a148c524102d4800598fc0b11f013a3d026c7804c1040842001043f02007c0360f406a1e00d03b0148740280e40101c55703792806cf440d58701a196c33327864621854c40188d6c301ad05e34f0b869c168d082c19b05631f0a863c148c682802d04e04e0980841280d82400f04601b08803410c940207a203ec4f0798860eb0e01c4a78369430692580c8d3c181a182e3370586560a8c541418a02604f0480860880dc1001581e01303801f064942097a201ac4f82d8860630e00b4a7814943025259030d3e051a1c1033781c657010c560118a01004f01c0860300dc0501580801300c01e0100240100400007f 16 6 13 9 1 7)⟩
def c4Bounds : List Bound := [r1,r45,r21,r31,r26,r27,r24,r46,r47,r48,r49,r50,r51,r52]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N0 : treeBlock 0 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N48 : treeBlock 48 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N96 : treeBlock 96 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N144 : treeBlock 144 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N192 : treeBlock 192 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N240 : treeBlock 240 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N288 : treeBlock 288 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N336 : treeBlock 336 48 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4N384 : treeBlock 384 15 (caseNode c4 c4Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B0n96 : treeBlock 0 96 (caseNode c4 c4Bounds)=true := @treeBlock_merge 0 48 48 (caseNode c4 c4Bounds) c4N0 c4N48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B96n96 : treeBlock 96 96 (caseNode c4 c4Bounds)=true := @treeBlock_merge 96 48 48 (caseNode c4 c4Bounds) c4N96 c4N144
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B192n96 : treeBlock 192 96 (caseNode c4 c4Bounds)=true := @treeBlock_merge 192 48 48 (caseNode c4 c4Bounds) c4N192 c4N240
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B288n96 : treeBlock 288 96 (caseNode c4 c4Bounds)=true := @treeBlock_merge 288 48 48 (caseNode c4 c4Bounds) c4N288 c4N336
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B0n192 : treeBlock 0 192 (caseNode c4 c4Bounds)=true := @treeBlock_merge 0 96 96 (caseNode c4 c4Bounds) c4B0n96 c4B96n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B192n192 : treeBlock 192 192 (caseNode c4 c4Bounds)=true := @treeBlock_merge 192 96 96 (caseNode c4 c4Bounds) c4B192n96 c4B288n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B0n384 : treeBlock 0 384 (caseNode c4 c4Bounds)=true := @treeBlock_merge 0 192 192 (caseNode c4 c4Bounds) c4B0n192 c4B192n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4B0n399 : treeBlock 0 399 (caseNode c4 c4Bounds)=true := @treeBlock_merge 0 384 15 (caseNode c4 c4Bounds) c4B0n384 c4N384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c4Proof : Holds (caseBound c4) := caseSound c4 c4Bounds (extendKnown (bound:=r1) (extendKnown (bound:=r45) (extendKnown (bound:=r21) (extendKnown (bound:=r31) (extendKnown (bound:=r26) (extendKnown (bound:=r27) (extendKnown (bound:=r24) (extendKnown (bound:=r46) (extendKnown (bound:=r47) (extendKnown (bound:=r48) (extendKnown (bound:=r49) (extendKnown (bound:=r50) (extendKnown (bound:=r51) (extendKnown (bound:=r52) (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) r52p) r51p) r50p) r49p) r48p) r47p) r46p) r24p) r27p) r26p) r31p) r21p) r45p) r1p) (by decide +kernel) (by decide +kernel) c4B0n399
def r20 : Bound := projectFact 0xffffffffffffffff0000000000000000ffffffffffffffff [0, 1, 2, 3, 4, 5, 7] 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r20p : Holds r20 := dagShiftLower (width:=256) [vs01,vs35,vs46] c1Proof (by decide +kernel)
def r39 : Bound := projectFact 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f [0, 1, 3, 4, 5, 6, 7] 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r39p : Holds r39 := c3Proof
def r40 : Bound := projectFact 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff [0, 1, 2, 3, 5, 6, 7] 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r40p : Holds r40 := c1Proof
def r53 : Bound := projectFact 0xffffffffffffffffffffffffffffffff [0, 1, 2, 3, 4, 5, 6] 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r53p : Holds r53 := c4Proof
def c5 : FiniteCase := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,[0, 1, 2, 3, 4, 5, 6, 7],13,2265,[1538, 263681, 526849, 791041, 1057281, 1328130, 1606658, 1904648],⟨[3, 5, 6, 9, 17, 24, 34, 66, 96, 136, 160, 255, 10, 33, 44, 52, 76, 146, 193, 212, 0, 80, 132, 1],rfl⟩,(0x2019090c4824a2218028181422000052210818091a07180a02080c420512088906018060422a142802422482218242050181029100a4040b00088681641280580e4122090421408824180209500832010c40230804c100b0201c02290082c480640a8082601804442091402502882611458250601524912090842220904442030601804230002400030508848050500c14096a3d1a8dc6a359a8d5683c1a0d868349a0d16239188cc6231988c560b8582d160b2582c560b0d80e06032180c24a2d1289c4a25928954934924b24926924964924d20b048261209142291088c4221908854130904a24122904864120d02a140a45028940a1502834028100882a1d0a85c2a158a855281c0a05828148a05126330986c26170984e2613490c8241a090582412890492219088462211482612094482492091482432018080421a2d068741a0f068361a0d460b0181c06038180c86031162b0586c160f0582e160b450a8141a05038140a8502912290486412098482510a844261108c4422910894422310280406010088281c0a05828150914824320906824160904c201808044188c06070180e06034148a05128142a05068140e0502c1088040601009020180805011080422010180403008440209008140203,207),0x4205014201088007fffffffffff8042000421084410008820006204100420108800fffff0800800fffffff42108441080080201409b8d45226088911110908908851084485ffffffff0800802064208010420204803fc103ffc0083fc84083ff210081ffa08808acc1938c82c38010a22112112108a27fe08109ff808212fff808049008508240e084f0f10f10f108f0f8388f83e0f08711e10c888452b3acfd801bb4444125f05f08442120a210844095f0bf178e14c01c03fe3bcddc447e042443f044213f0210847f04288251f,0x201814201088007fffffffffff8000000000000000000000006264100420108800fffff0000000fffffff00000000000000000113704a4209c8a080000000000000000001ffffffff0000000064209810420204803fc003ffc0003fc00003ff000001ff8000000482460b02017045800000000000007fe00001ff800000fff800338800508240e084f0f00f00f000f0f8380f83e0f00701e00c010000925200002496000001f01f000000000000000001f03f078100c4400006d43400003e000001f000001f0000003f00000000f,(decodeNode 12 25 0x12507ad7a23d0bd11e740b0f363347973143bf8ca1dfcc50ef46287787a23b83d11db9e88edaf4476a7a23b398a1d8d258ec493476100e3ae8d91d486b0ea43287527a239dbd11cd1e88e6663472d7a23928161c846b0e3632871b02c3848d61c00650e00f446fc1b237d0d61be86b0dea0106f502c3791881bb0c40dd63416eb3103738d61b81e88db83646da1ac36d0ca1b68c98daa64c6d302c3688d61b3c650d9e34c6cb1a63640c51b14682d883146c418a3619881b08682d843146c23143608d61b00650d803646ba1ac35d0ca1ae80b0d6e3416b33103580d05ac0082d5c6646ab32c3559901aacc68d566286ab18e3558d61a88650d44f4469d1b234d8d61a6c650d3601069b7a234ca4b1a64048d2e0286940143498161a3de88d0ef446827a234080a19f8038cf40406740203390c719acc50ccef446657a23298c5194de88ca43146527a2328a4b1944628ca2034649008321a4b18e4c40c7203163900431c98818dc062c6e00863731031b00c58d8010c6c63463519431a00f58c8c80c5e32862a01430d80a1858050c2602861001430600a1821e88c04f446007a22ffbd117f8050beaf445f44962fa00757d0050bca01c5e27a22f0bd11779e88bbaf445d50142e6bd11720050b8af445c44962e20075710038b72f445b67a22da3d116c9e88b600285a57a22d080a1679e88b3a92c59d00eacebd1166de88b32f445977a22ca3d11638050b14f445860142c1bd11609258b0401d5827a22c03d115d40c8ae60585737a22b6a4b156eab8a96f4454b4962a5bd11529258a94f445497a22a43d1151d258a8e3645461ac2a30d9150c6b0a866345421b22948d614a4650a532505241b22908d61484650a4236451c1ac28e0ca14706c8a3035851819428c0d9144c6b0a263285131b22870d61438650a1c3645081ac2840ca14206c8a06358503194281bd114046509ff55c4df7a226f55713712589b92504d892826bbd1135de889a0f444cc7a226524b1329e8898af444c37a226024b12f805095a02849a032245bd1121de8890af4448303223f3d111ede888f2f4447702c23900a11c80b08dc01c4687a223124b11892588b6f4445a49622d00711200b088605844103221e01010f125886e92c43661c21aa4b10d525886692c43249621880a109de8883892c41c03220da4b106408082e0404120122083d1103d25881662040b4961f93d10fc52587e26203f11a61f79930fb52587d86203ec0141ef00a0f6c0507880583b70141d900a0eacc407483293a20321cf8c74e7465473955c39b61c1cc8078e500c87260583930151c98190e480c872292c3909281c65570e2de8871607038a9281c4bd10e264a07100643880271c43d14e1de8870ec383879281c30034e124a0704f443829281c024b0e024a06eef443774a09bba4b0ddde886d925036a00f1b50134da00546d12503650151b2c940d900546c807036302c1b18130d8c0806c601c3633141b0a4d0d7cc686be92c35d4961ae2524d6d2586b6c3835a4961ad3150d652a86b292c3584a49aba4b0d5e4a06a955c3537a21a9a4b0d4de886a492d3524961a93d10d458706a292c3519281a83d10d3d25869ef4434e4969a724b0d38c6869ac3834c49b1a618d8d30c68698c543490081a38044d1802068d2503453381a19990d0cc6868725033f61c19d0c50ce24a066ec3833732519b9880cdc69466e04c33202019901c0cc40c866206432e0201974940ca64a064af453247a21924940c8e4a064403d31d7a218e0100c6a4a06292503114961884940c3a4a061b25030c0321860100c30c686132503087a2182c940c124a06052503010321808100c040805fa6282fc1b817d0d90be86505f4c542f800817b0070bd40c85e80102f133217798d0bbe4a05d60102eb00e1748068ba00365cf2502e67a21731934b946c85cb2502e47a21720d24b906825c92502e01b216e8d00b76ab85b92502dc7a216e0d04b706c85b03402d81b216a0d60b506805a83342d419416a0068b480365a32502d07a21681934b3c6c859e3582cf1a01678cd0b3e4a059cf442ce1a49670d04b39e8a59af442cd4961668d0cb3467e59a01a2cc00d965c940b29e885943492ca7a2964bd10b264a0590f442c83209641880b2125858e64d2c71b21638d60b1c68058e3342c71951638ca0b1e4a058c94e2c64961631938b1a4a058af442c51a49628d04b15e8a588f442c44961620d0cb1067e5880182c300c9612560afcce057e6642bf32615f98d0afe4a057b2502bb7a215d8cf4aec6285766582ba1b815d0d90ae86985743402ba19a15d1934ae4c405723642b91ac15c8d00ae46505726542b81aa15c0d30ae24a056ec382b731015b8d38adc69456e01a2b600d95ac940ad1e8856864d2b31b21598d60acc6805663342b31941598044acc0205672502b23271591928ac809c564f452b17a2158810cac407e5620132b19281583d10ac06925603412b018a1583d14abde8855e92c2af1a19578cfcabc62a55e3142af03815730e0aacc6c5566312ab01b155b0e0aa587054e0402a30181510060a8806854001c2a092814f0138a780e053a04c29d92814e0100a7009853003429862a14b4940a440805220282919281484940a31870518c3828531b14298c8a1405450a03428400e14224d0a08668504034282012140c940a0004a50125027e1a013e80d09f40504fa01c27d61c13e0ca89f006c4f803227c4a193da4fc9ed25a4f692c27b31593d989c9ec03e4f603427a92813cb0e09e40524f201d27900e13c19509d80504e434027119a1388ca09c64a04e0c382703101380d009c06684e032827031413600a09b06924d6c4c26a928134bd109a407a4d200d269928133b0e099c66c4ce648264014132494098de884c6941263496131810498c03a4c60112634961310cf49886284c403426201513100a09880384c4c542614a493024b0980c804c062026000c93000209800684bd25025d61c12e98809746944ba05825c02612cc9409580504a7250251310128c94093c64a49e31424f01412700d092c020497250249327124988092409c49355c2489281241938920c4049004e248928123188091a4a048a64e24531012281389164a048864e24431012201389124a048464e2423101210c5090809c48525023d92811e01908f00b047804e23c02611e01008f006847803423800811c49408d006846201023192811830e08c005246001123000811849408b802045c95822a4a611525008a8c504552602293141145570899e8844c92c22592811261a088d87044662022301b111804088a4a0442010221aae1103d1088125844092c21f7a290dbd1086cc5043325021892810bbd14859e8842cc3821661c10aa4b08564a042892c21392810949408458704226202111a710880d8845e8a420f442104961080d0c84067e42031521018a108004083e4a041d25020d928105c94081cc5040b2502049281000c508000203ff2501feaae0febd107f52583faf441fc4960fe24b07ed2583f4f441f94960fc98a07d64a03e8f451f37a20f9a4b07ca4a03e292c1f09280f7c9407b98703dc6201ee1a70f73d147b5e883da92c1ed1a18f68cfc7b462a3da3141ed9280f600407b2ab83d692c1eb7a20f524b07aa4a03d2f441e84960f418a0799e8a3c8f441e49280f1993878d2583c492c1e19280f030e077cc403be0361df7a28ef3d107792583bc3431de19f8ef0c547786283bd2501dd0060ee80707700503b40281d90320ec01607600843b002a1d80210eb0c707524a039c0401ce00c0e680947300323992501cb0270e580a872e4a03940401ca0320e4b0e070d870380c381bf3268dfb0e06f125837864d1bc1950de00a86f187037434d1ba9280dc49406d066a368c381b20148d900a06c8ce035c6641ae31a0d731606a4c5035293e1a77a20d2996068c6e03463641a31a00d18cd068c6503472501a261c0d10d906886b03443401a219a0d10ca06886903432501a04960d00cf86818a833e35819e1a60cf015067401833ac381993100cc8c5066407a32af441949280c98dc06446c83223281919280c80d386424a031e63418e3380c51990628c6831431c18a7a28c43d1062068631033f18818a8c4494061de9e30ef451877a20c38d3c61c68630e33f18718a8c3c940619e8830c34118619e8c33d14615e8830a34318519f8c28c54615e8a308f441841a18c20cfc61062a308f451837a20c18d0c60c67e3063151839280c11938608c4030434e1821a50c10c50609e8a302f441811a18c08cfc60462a30231418101a0be8d505f00482f402517932a0bc24d05dcc682ee3341779280babd105cd2582e69581729280b825005bc0682dc37016c1b20b60d305b06802d833416c01e0b5c9405a864a2d464016961c0b398d859e4a02ccc381669280b1b0e0586ab82c0f5b1607a28b03d105812582c034316018a0b0494057de9e2bef4515f7a20afa4b057c6862bf25015e7a20af24b0579e8a2baf4415d4960ae8d0c575e8a2b8f4415c4960ae0d0c5706282b925015b18a0adbd14569e882b492c15a1a18ad0c50569e8a2b2f441594960ac8d0c5646282b2f441574960ab30e05452582a264d15119b0a88ca854463c2a231c1504960a78d0453e4a029837014a1b20a50ca052802029403c1499280a2c9405086e028036414019a0a00040501e8827e92c13f02089f8d304e24a026cc3813632709b49404ca4a026292c12f92809730e04b4c4025a01e12b01509501084a408425002a128032093807849c01c24d250124928091a4b0488656244c38121018890803447de8823c64911e92808e819047409c23a04011d92808e010047004c23601a11b01388d006c46801e23402a11992808c019046009c23004011892808b810045c0c822c05911502c08a813445401c22a00e11462c0890d504464a021ef4410f1ac086c94043187021800810c928084b0e042525a21092c108496883a4b041c68220ec3810649608324b041125a20692c103315881988040c68220601f10349608100f040407a2000311007a207f98d03fa4a01fa04e0fd7a207e49403ec6e01f23640f91a607c8ca03e64a01f12500f461c07a49403cde881e63290f302487980303c804a1e200d0f102a07824d03bcc681df2500ed012876bd103ad2581d63490eb61c07519903a8cb01d46400ea31b07518d03a8c501d431c0ea92807431383a129c1d092c0e8198874494039cc9c1cef440e649607301243980501cb2500e401a07180a038c0681c52500e161c07098d838409c1c20290e1014070c9403800921c06280df62706f006837801c1bcf450dd7a206e80fc3740361ba00f0dd61c06e18c03718701b60360db01486d80a036c0101b6f440d992806c30e03624a81ae3480d702a06b81503580181acf440d549606a812435401a1ab2500d161c068996033c03819e9580ce626866b0e033462819892d0cb49606598ac32cc401963410cb1958658c9c32c63e1963150cb18a065b0e0328c401943140ca01e06480f43224a018ec540c61b80628d9031465018b2500c461c0620d383100781872500c249606100c4308ce017c6640be31a05f49402f52801792500bb19a05d3d102e46281732500b818a05c00902dc01816e0250b600685b49402d40a81683700b31b20598cd02ce4a0162c380b100c85880342bd26815a6340ad01a056c9402ae4a01512500a761c0538cd029865014d2500a461c0524940289e8814492c0a218a051012428807a1440120a29280500c502824a013ec3809f31b04f803427c0e013c06509d03204e80482746b013601e09b00f04d24b0264056132c3809819b84c003025de8812c6490961a484b019025409c12a04009500904ac94425009c12801e094013049806824c01c12600f09201504880782464a2121250090032848019024009e12004e090020848010024003c12125108f928047813c23c09c11e02b08f01504780d823809a11a03708d01b0468078236ab811525008a62c04518a02286521140540899280443d1022127c11004a088aae043c94021d8b410ec4e087626043815821c0a810f2510869280433d1021809610c04908601e843006c21801e10c949085496042b1542118701086580841b80420d9021068010833608419a0420ca02124a0106c3908361c0418d9020c6b010634008319b0418cd020c650106c5508262a04130e020929810492c08200e03f49441f64a00fac3807d32783e992c1f58700f892c07c19483e01341f18720f6c3807b31b83d98d81ecc400f633707b19b03d81341ec0780f401a07a01f83c80f41e40360f200f07992803c0d541e24a00eef440777ac03b0cd41daab80ea04c07592883a49401d009c0e804107402003a00d41d003c0e92500731aa83981501ce4a20e525007262703931501c58700e292c071aae03831581c2ab80de64106f3200378d681be4a00dcc3806e1a703755701b58780da33006d01e036c9441b24a00d8c4b06c61c03625381b12960d893006c4960360c9c1b064c0d803206caae035c9401ad8b00d6c3806b4ab035a4b01ac6aa0d634d06b19483580781a804c0d2027068aae033c94019c0380cd55c0659280329954194c9a0cb25106492803230e0190c9e0c864b0647a2831bd1018c6860c633f063021831c940189e9e0c4f450627a20310d3c1886860c433f0620218314940185e880c234106119e830bd14181e880c034306019f830010c181e8a0bef4405f1a182f8cfc17c0860be02905f7a282f3d10178c860bc62005e1a182f0cfc17863e0bc04305e01482f49441764a00ba64f05d32702e992c174c420ba62005d1a782e8d381746960ba34a05d02782e80d4175e8a0b8f4405c1a182e0cfc17062a0b831405c02182e00a4172ab80b665505b32a02da4d0168c6a0b463405a01a82d00d0169eb40b202605901202c80601664a20b125005802582c009c16004a0b001b05800c82c003c162ab80aef5a0577a202bb0e015ccb40af25105692802b31381598960acc3805649602b55701552b40aa9410554a002a9968155e880a894205449f02a010815006a0a803405400882a313c14d8960a6c3905361c02980dc14c06c0a603305301482980a014c0260a6011053aae029494014989a0a4c3805232482918d8148c400a43560521aa0290cdc14a4a00a2f440514a5828a50414525a0a292c0511a58288cf41446560a232705118a8288c501440940a202b051015028bd101412580a0358050021028557013deb409ef4404f61c027996813cc8009e63d04f318827988013c68209e33c04f19a8278cd013c0b409f55c04e4ad02724b01386b409c07004e03202701681380b009c04c04e01a027007813803809c93404c01a026494412a4a009401204a00682530e0126ab8090f440474960238d0811e4a208d25004661c023193c118c9608c62104631002361a011587008b55d044aae022256c1112ae08894304449f82224b4111258088043044015822004c1124a0086c38043032021816010de8a084f4404262182130e010928608493f04249b82124b4109258084343042195821010c10805608401304200882155701040e008206404102d02081301064a208125004062702030e010129c08094a0404960200d3c10009e08001304000882049400fd87007e06403f02c01f81380fc09807e04003f7a281f3d100f928607c93f03e49681f24b00f868607c32b03e02181f00ac0f802607c01103e61c01e81900f408007a03603d01a01ea50c0f127e07892d03c49601e18ac0f0c4007804303c01581e004c0f0022078c3803b01301d00300e807e07202703900c81c803c0e401a07325003832a81c01500e126806e63503719a01bd5700d801806d25103592801a80640d401a06b55c03492801a30e00d06b406835603402a81a01500d1e8806695903333801999900ccc9806664003331a0198c740cc63806755c03201e01955700c528206265a03118e018bd100c001806155c02f928017b0e00bccaa05e64d02f9288173d100b929e05c94b02e4a181725040b925a05c92c02e1a78170d2c0b869205c34302e1a08170cac0b864e05c31502e61c01698840b466c05a31e02daae0160d680b24a205725002b627015a4b00ac69e05634b02b1988158ca40ac62a05725102a928015193c0a8c9605462102a1b20150d600a869c05434c02a1a00150ca00a863c05431c02aaae014bd100a52b405292c0291ad0148d080a64a2051250028627814312c0a1872050c3802832781419380a0c9605063702831b01418cc0a0c4205034f0281a58140cdc0a066c05033302818a8140c500a0032051251027928013b0e009cc9e04e6200271b20138d6009c69c04e34c0271a00138cd809c66804e3280277a201324b009802404cf440254ac8129908094c5404a03402501501280700964a20492500244960120d3c090696048315024aae011996808cc5404601c023928811494008987004434f0221a5811013808aab8042f440214960109968084c8404233e02102d010807408403804200802192801030e408187004063602019b810013808006c04001202000d00f803807c06603c01b01e00780f4940075e8803a34b01d1a480e8124074c5003832901c92880dc94006d89c03601a01b00700dbd14069e8803403f01a00d80d003c06a4a20332500197a200ca53c06529603294301949680ca4b006409e03204b01902480cb0e406187003064d0181b200c0d6006068003033601819a00c0ca006002003125101792800bb13805d89602ec380174a700ba4b005c69e02e34b01701880bc94405a4a002c64f01631a80b0d3805a4a202b25001562780ab12c05587202ac3801532780a9938054c9402a63701531b00a98c805409c02a04b01501b00a80cc05401e02a00e0154a180a24fc05125a02892c01400980a003c051e8802692c0131a48098d0c04c62a02631401362680930e404987002464d01231b80918cc048c4202462001201b00900a004803c025251011928008a4b004469e02234b0111988088c54044628023251010928008193c040c96020635010310808188004069602004e01000f008494403e4a001ec3800f1a78078d2c03c62a01e31400f928807494003989e01cc4b00e61c80730e0038c9e01c63700e31b007188003869601c33300e18f007013c03809c01c03700e01b007002003a4a201b25000d027806812c03409201a62800c014806494402d89c01601a00b007005bd14029e8801403f00a00d805003c02a4a20132500097a2004a53c0252960129430094a0804a4b402525801234f0091a58048d24024656012c3900861c00418dc020c6601034d00801b00400780224a200f250007627803b13801d89600ec3900761c003a53c01d25800e34f00719b8038ccc01c66200e32b007194803813c01c09600f251006928003193c018c9600c34f00619a80301900180b000c04e006026003010001805000c01e00600e003313c01589600ac3900561c00298dc014c6c00a633005310802988001409e00a04e00502580280dc01406600ac4f00462580230e401187000834f00419b8020c7c01063a008065004032002010401008000803700401b00200d401006800802900401400200200124a2007250003627801b12c00d872006c38003327801992c00cc6e0066330033108018d3c00c69c00634a00319b8018cd800c66400631f00318f0018c6800c09c00604b00301b00180cc00c03c00601b00300d001bd14009e8800494300249f80124b400925800434300219f8010cac00864e00431500218a001010c00807e00402b002013801004c00801e00494300149f800a4b400525800204300101f80080ac00404e00201300100780080240040100020ff000),graphMoves,(dagLookupLinks 0x29be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029be0537c0a6f814df029bc0d3780a6f014de029bc053741a6e814dc069b21d3640a6c034d60a9ac053541a6a814d30a9a60534c0a69814d2069a20d3440a68814cd129980d3300a65834cb029960532c0a65034ca02994053280a65014ca02994053280a65014ca02994053280a65014ca02994053280a65014c906992053240a63074c50698a053101a61054c1069800d2fc1a5f034bd069780d2ec1a5d034b70e96c0d2d41a5a034b20a964052bc3a55894aa069520d2a40a53074a5069441d2880a4f8749e0693c052741a4d85492269220d2440a488148f0a91c0d2341a460348a0a914052280a450148a02914052280a45014870e90e0521c0a43814870290e0521c0a43814870290e052103a420148402908052100a420148402908052100a4201484029060d2081a400548002900051fc1a3f8147f028fa151ec2a3c85479028f2051e40a3c81479028f00d1e00a3c01474128e8051c04a3609468128cc151941a3281465028c80d1900a308745f0a8be0517c0a2e8545d028b80d16c1a2d8145b028b60516c0a2d8145a068b4051641a2c03458028b00515c1a2b81457028ac0d1580a29874500e8982512c1a250344a02894051202a24014480288c151102a220144012880051000a20014400287c150f80a1e8343c06878050f00a1e014390e86c1d0c84a168b42c068560d0ac0a130b4260284c050980a13014260284c050902a120142402844150802a100141c12838050700a0d0541a02830150600a0b054160282a0d0540a09074120281e1d03c0a070340e0281c050341a05074041a8021cff449fe033f7167ec0cfd029fa013f4027e804fd009fa013f0127e004fc009f7833ef027d81cfa439f2893e4067c60cf7859ee833d9127b204f6409e98d3d3027a604f4039e8013d0027a004f4009e8013ce0a79c04f3809e7013cc0a79414f2809e3093c60278814f1009e1833c30278604f0819e0833c10277e14efc09df033be0277c04ef809df013be0277c04ef419dd073ba0277404ee809dc053b60a76814ed009da013b30676604ecc09d9033b1067600cec009d7833af0275c0ceb419d6033ab0675604eac09d5033aa0275404ea809d4833a90275204ea409d4033a80274824e9009d2013a40274804e9009d2013a40274804e9009d2013a40274804e9009d1833a00e73e0ce7039cd053980a72824e5009ca013930672604e4c09c981393027240ce4809c9013920272404e4419c8033900271e0ce3c09c78138f0271e04e3429c5073870e70624e0c09c00737d0e6f80cdec19bd813790a6f204de409bc03378026f004de009bc01377066ee04ddc09bb81377026ee04ddc09bb81377026ee04ddc09b88d370066e004dc009b78336f026de04dbc09b78136e066dc04db809b68336d026da04db019b60136c026d804dac19b58136b026d604da819b50136a026ce1cd9039b201363066c604d8819b083360066b434d6419ab853540e6a60cd3c49a6073481268c14d0c39a0073400268004d0009a0013400268004d00099f8333d0a67a04cf4099e8133d026780ccf0099d833361666a0ccd4099a03333066640ccc80998053300266004cc009980132c1265414ca809950132a0265404ca809950132a026520cca40994813290264e14c94299281325026480cc843990813210264204c840990813210264204c84099081320066362cc6c098d03319066300cc5c198b813160662a0cc50198a013140262804c443988813110262204c44098881311026200cc4009880130e0a61814c3009860130b066101cc0c598103302026020cc00197f832ff025fc0cbf4197e812fd025f02cbe0097c012f7065ee04bdc097b812f6065ec04bd8097a052f20a5e404bc80978832ee0e5d814bac1975812eb025d604ba42973852e7025ce04b9c0973812e6065c814b900971052e2025c404b880971012e1065be14b7c096f812df025be04b7c096f812df025be04b7c096f812df025be04b7c096f812df025bc0cb78096d092da025b404b64196c812d9025b204b64096c812d8065ae0cb5c096b812d7025a42cb3c3965892c80e58e0cb181962052c20a58404b080960052bf0657e04afc095f812bf0257e04afc095f812bf0257e04afc095f812bf0257e04afc095f812bf0257e04ae469598d2ad1a5541caa80954832a90254c1ca980952052a40254804a882951012a20253e1ca7c094f8129f0253e04a70394e0129b0653604a60394c012980252e0ca5c094a072940252804a4c1949812900e52004a400948012900252004a3439468128d025180ca30094487289025100ca200943832870250e04a1c0943812870250e04a1c0943812870250e04a1c0943812870250e04a1c0943812870250e04a1c0943812870250e04a1c0943812870250e04a0c493f0b27c0a4f8049f0093c872770a4ee049d0393905272024e4049bc39360726c024d8049b009360126c024d4149a0293401268024cc149902932012620a4c4049880931012600a4bc14978092e0525c024b414960292c012560a4ac04958092b01256024ac04958092b01256024ac04958092b01256024ac04958092b01256024aa0c954092a81255024aa04954092a81255024aa04954092a81255024aa04954092a81255024aa04954092a81254064a804950092a01254024a804948292901252024a404948092883251024a204944092803250024a00493829268324d024980c92c192485249024920492409248124806490049182922052440248414904191f8523f0247e048f0391e0123a0a474048e8091d0123906472048e4091c8123902472048d8391a05234024660c8cc09188522f0a45c0c8b419160322c024521c8a40914032260a44c048941912812250244a048940912812250244a048940912812250244a048940912812250244a048901912012240244804890091183223024440c8880911012220244404880291001220024400486c590d032190642e1485c090b03215064280c850090a012140242804850090a012140242804850090983213024260484c090981213024240c844190881211024220483839068320d024180c83009058320b024160482c09058120a06414048202903832060640c0481809008b201024020480409008120102402048040900812010240204804090081201024000c7fc18ff031fe023fa0c7f408fe031fc023f8047e438fc811f60e3e4247c808f8831f1023e00c7b828f7011ee023dc047b808f7011ee023dc047b808f7011ee023dc047b808f7011ed063da047b408f6031ec023d8047b008f6011ec023d8047b008f6011ec023d8047b008f6011ec023d8047b008f6011ec023d8047b008f6011ec023d8047ac18f5811eb023d6047ac08f5811eb023d6047ac08f5031ea023d4047a808f4831e9023d2047a408f4811e8063d0047a008f4011e8023d0047a008f3831e7023ce0478858f0831e1023c20477448ed071d6123a81475008e9831cf1239a1472c28e4071c7063862470818e1011c20237e1c6f428dc0b1b60a3622c6b058d4871a70a3385c66438c90f1900a3143461c38bf13179162f00c5c868b90116c1a2d80459868b301165062ca0458c28b00715f062bc0c57418a91714f0e29e0453c08a68514c062980452c18a485149022920451838a3011430e286044e898998f133022601c4b048930d1260224a0c490188f0d116222281444048858b106162061c3f8587c0d0ef261da1438ca86e0f0d42219e2c3381865090c222180142ccd859030b10615e142bc0857030a71e1462428c084e8d09c061360c268184b87097021242c24808488308d1211a0423018421108402108042100841050800a0fc141f8083f0107c0a0f4141e4183c81078060ec141d418361306c020d414180a82f0505c0a0b804170082d8305a060a834148282901051060a20414018280104d0e09a041301826010461a08814108281f0903d060780c0e0481c0102e2a05a0c0ac28158102b020521409c2813810260604424088081101022020420c08018100101d0e03a0406c280d81016160222c03058040900021ff433fd457f70efe915fcc1bf8067ec8efd60df9c43f2457e20afbd1df6653eb077d38afa605f4813e8047cf82f9c0df2843e3477c602f8b05f140be0887c082f7e0defa0bdd487ba80f6f19ed233d8487ab16f4f1de903bd00879c10f311de5633c80b7899af0e15e0e3bc00777f04ef71ddea13bd0177610eec01dcc33b94176e90ed61dd965bb1857600ceba19d6833ab0875096e9921d2243a2877418ee8205d00139f0473a10e7401ce21b9c0173686e6c05cd8039a8273386e6311cb05b954372a80e520dca013930472600e4b05c960391c472380e4605c8c03908472100e4201c7c238f0271c86e3805c70038d0471982e3205c620b8b8371700e2c09c3a7b868370b86e1215c1e1b804e6ff06dfc09bee2b79526e632dcb05b8c2b71026e182dc205b7e1b6fc06df80dbc0db70236c476d880dad11b541b6a026d208da209b305366006c810d8f05b1a1362836bf96d781daec135a8c6b482d6709ac03b57c16ae06d5c01ab60b56c06ad80d5909ab00b56006aa86d5501aa61354c06a788d4e05a922b510569e10d3715a642b4b0669600d290da482b47c568f80d1a15a283344c168788cfe459ee3b3c076758ace6159c22b364866a0acd10d9963331c466206cc10d9782b2cc96570aca71d94e03288565082c9d119380b26c164d02c931d9240b23c36448cc821d8f63b1e0363b04c72118d0531a006318ac63018c40b180262f04c55258a223140162782c4c0d88e2b100761d8ac3a058720b0e4061c02c38018623b0c4061784c2f0185c0b0b0261600c2c01858030a826120cc1d1d8341b060260b82c150982613040360410c080180e0b01425fe90bfa0d7f20afe015fb04bf2117d63af9075f086bdf097bc0af7025ee00bdb057b01af34b5e584bc9097900af1435e00abb91d76e12ed815da82bb4057660aeb465d680bab097540aea415d402ba60974812e8825cf86b9c0d7321ae4095c608b890d70c1ae1415c106b82017020ae0015bf04b7a116ee1adc075b410b66096c812d64b5ac80b541569e2ad3035a582b490968e12d0c459f0ab362166c02cd8059b00b321166402cc805960cb2b056501aca0059286b250163c3ac74158b0eb0e2161812c14758202b02095fa2abec257d02af9055ec1abd8057b00af5055dc3abb0257504aea015ce1ab94257184ae1095b632b5075668eac32957a32adc655712aa81954432a70654b0ca901951432a28054500a8a015120aa1c254380a85094fa429f0153c86a79014e43a9c415360aa6b054d21299c253284a64054c60a978552e04a590d4b00a96005298aa500d49432908851d10a34194545288c750e0ea17154242a834550584a06154022a80014fe869fb093f2127dc24fb029f30d3d83a7a824f3089e6013c81278824f1009de113ba0a77014ee009dc013b41276414eb849d40d3a60a73c44e50a9c9053900a71c14e2849c50138a0270c24e1809be1537a0a6e444dc809b60d36a0a6d404d9849b20535e1a6b814d40c9a50d3402a66864cb0898e2131c0262c34c48498415300225fc14bc8c9760d2e4225bc34b50a961252be1256854ab869560529a4a51c64a302945052880a510049f0c93d052780a4d474990692b1d24e22480748c10914112260a444248316904092021a3e0947b048f5051e2223bc2476848ed011d22239c2473028e4091c802384346d8c8d80d19e4a3303465048c90518242304045d8c8b321166022ac8454848a60d14a0a2901451048a1051324224874488288b191005a1f044389686e0d0d61a19c443206862090bc22174142e02858110a82214c14280684d0d09222120141e188371506c0a0c844178682e050561a0a03413828240d0460a08034100081d0d03612064240b84816050281204824080480b150101a01c1402068030500019ffc13fc0e7f800fea19fd403f80a7f000fe001fb823f5087e610fcc01f8c33f1807dc1cfb801f6823eb087d504f9459f2413e2887bd20f6849eb083d11479534f1c39e1883bc9a76e2cece39d5913a39e74214e6091c84f38f0671038e1821c00c378206da58daa29b18f35aa26a054d3a19a5c63490a69104d0e519f893381c66238c9ca192843211063d14c74198a513120a61734c127181052fe105f420bdc3176552e59c5c908b78696c0c2d02058d4cafe715d0b2b59255f30aac4953492a19453634a44a1460a284204fe289dc81351a2639a4ba3495481261223a4845e5889891118621a2442734840390608207143f6607dc40f90a1eb9a3cc2c78450ebd31d3123954471c38dfcf1bb90369386c048d3921a60433c4064cb0c78818c8a311205fc98ba5516d1e2d02859238ac19153922905c51628a18513c1c26a384c63891dc11d1a2361045c4089c71108c2192041c5881880fb9e1ea343ba6876050e59a1be3434eb8660f0c3a21801c2cec855d00a88c14434278404c4b09490117481fec03d89072a20d63c174e02b8c04a34082480c6f810e0013b801548002a00001 0x1100010c6c3d12fd462046c4942fd262043f0c7afd6620bf3a4b0fce62046b8d3305292c3f318811ae36446bbd111acf44c1424b10fa6293f298811acf4446a81611a83344360c711a63584680cd11a23284690d6318464046998a11a4328c6099010d431c4348c711a063446898a10cc31c46818a10c631c467a56119a94c465a50104a3144120c51046314467b0e1044314467bd131866424108c5119cf44466b0e10e631d4100c5119cf44466bd11198c384388c7503e3144663d11196c384378c7503c314465bd110dc31d40e8c510be01046518a319494c46518a3190f44464a4b1190620c600d0703031446000750c0012c30004503000846424d118ec38bed188118e01c463007118a01c42e0c7118801c4630d9118a3584620ca104ec38bf09880fd03144618d33038008461bd13036008415b0e11843644608d31184f44c0d0021182f44c0c802118063445f019117604045980a114e01c45e819117404045700a113401c45e019117204044d80a113201c45c193115a64044418d117e31c45fbd12fc062045518a117c058c5b8d63158328c4c004302e31440b802117a35845e0ca1028620409802102000840680210180084058021176058c5b0d63156328c4b804302c31445b80a5014008c5b0d0701231445b00a5012008c090c5301e31445d0d6117232845c30e2fbc62045c3d12fbe62045b8d9116c358c580ca314801045a8d61168010beea4b11660584591991162658c4f0c71160358c550ca312c010459188302a31445600a500e0084589881160341c040c511560294030023022314c070c5115e620c550d0700a31445500a500a0084570d61136328456b0e2fb6620456bd12fb86204560d911563584550ca31460104549961150628454993114c34c454193114a34c453816114c3584528ca31080104520d61146328c42004114834c4518d3114235844e8ca1122010451199114065844f990111a63444e18a111631c4510c5113002940200211423414500c5112e029401802113e31444f188113a34144e0c5112c029401002113662844d0d6113232844c0d9112e35844b0ca110801044a81611283584490ca11220104480c5110e02940080211283414478c5110c029400002111c3144468c511266204490d0511831444280a4ffe00844200d3122329c458c511220414458021120664447996111c64044698d11186284458c711066353ff18830d60084450d6111232844430e11066204443d111046204438d9110c3584428ca1108010441bd1110492c440809110002843f80a30fcf4443c0c510fc05843e8d310faf4443b98810d834243e0d310f633443e3d12fc631443dbd12fc431443d00a10ac31c43c8070fd801843a80d10ea63443c01010e864043b8100fd802843b0c710ea62843a3d12f9a6203e60c50fd800842e00f10e664c43899010de63443718d10e464043818d10da628439bd110e4314438bd110e0314437bd110dc92c4368c50ffa00842f00d10d8034c2b0d210d601042e8ca10d23344318ca10d004043280d10c40284338cd10c83284308c710d492c43498810d003143380210cc62043280c50c800843198810c403143080210c063442f8ca10bc03d42e80210ba64042e0ca10b606442d01610b204c42c01010ae02842b00710ae32842d80a10b402842c80a10b002842b80a10ac028c260d6109634c41b0d010aa3584298d310a434042abd110a8f44429bd110a4f44426819308e058c1e013108e04041e00d106202841880a108c64c418190108a04041d00d105e02841780a108864c41c990105c6344280c7108664041698d109e31c4210d0106e3344160ca10a20104160ca10a20284283d1109e92c4270077094658425193106a640bfe24b2ff692c3fd988109a02842630e109466442499610686404258c7109801c425bd11094c384253d11092f444243d12fee92c4243d12fec92c42318a4fe86204243d12ff092c42380a108cc38422188108cf44421988108a0284223d1108692c4210075082c38420199107e65841e99310666404208071080c384203d1107ec3841fbd1107cf4441eb0e107af44bfaa4b10766293f8988107802841db0e107262041dbd1107062041d00a1072f4441c24b106e01d41a999306865841a193106c31cc1b007106cf4441abd11068c3841a3d11066c38419bd11064c38bf7a4b306062a41818a4fde6204193d1106202841830e105c6204183d1105a62041780a105cf44416a4b105801d4158c63056018415bd11052c38beb9881050c38beb188105434c4153d12fb231441481910500584138d3104ef44bec188104c334c133d1104c92cbdb0c50f6c0083fe8c7103434040c8d01048664411196104064c40f990103c634411999104265840e98d104b55c4123d1104692c40e0d09044f44410a4b10363424103d1103ef4440f3d1103a92c40e0d9103635840d0d9103235840c18d102e3644098d6102034c4050d0100e3284020c7102c3644090d6101e34c4048d0100c3284018c7102a3644088d6101c34c4040d0100a3284010c7102e664409196100a628bea988102e36440b0d6102a32840a4942fa662040a4942fa46204098d910243584088ca10203644078d6101c328be8988101a3644060d61016328bea18810143644048d61010328be8188100e3644030d6100a3284020d910063584010ca0ffc6204008d910003583ff8ca0ffcf443fe8ca0ff69643fb2560fe894c3f7a500ff2964bf9a562fe094c3f92500fdc9343fe4940ff46203fe5570ff6c38bfc9880ff6f443fc9880ff555cbfcbd10ff292c3fc4940feec383fc4940fecc38bf91880fef2503fb3d12fe66203fab0e2f8e6203fabd12fe06203fa30e0fe66203fa3d10fe46203f9bd10fe492c3f8b0e0fe06203f8bd10f8e6203f83d10f8e92c3f7b0e2fdc6203f7bd10fdc620bf73d10fdc92c3f680a0fd80283f5bd10f963143e51880fd60643f50d90fd234c3f53d10fd2f443f40d30fd0f443e48c50fce0643f30d90fca34c3f33d10fae6203f2bd10fac6203f20d30fc8f443e41880fb0f443f0a4b2f923143f18160fc40283f08160fbe6583ee18d0fc001c3ef1960fb66343ea9880fbc6413ea1880fbef443ef24b0fa66203e91880fa26203eea4b0fb66413e81880fba92c3ee3d10fb692c3e78c50fb401c3ec8160fb00583eb8190fac0403eaa590fa89583e92500fa09343e798a0faa92c3ea24b0fa6c383e924b0fa292c3e824b0f9e92c3e700a0f9a3343e60cd0f9af443e624b0f723143e58190f9492c3e48100f90040be32520f8e0243e33d10f8a334be2bd10f8a92c3e21882f6c3143db0020f843343e08cd0f7e0283df0ca0f7a6343e1a4b0f826413de9880f8692c3e01904f786203e13d10f8292c3e01880f7c3143df8d30f7c64c3dea4b0f786203dd80a0f740283dc80a0f6e04c3dc0160f6e0283db00a2f54f443d524b292631434b804c926008a491882f652503d8b0e0f6a620abb0c5291c62034b0c7c91c31434a8cd4f68329a468c50d26012a461880d2231e3d98192e8694da44a4b0e8664d2449880f6431d2440c5292092c3d88ca8f6155cbd6bd1090c0082428022f58f443d7b0e0d200112420022f57250bd74940958620abf0c509026203d7007a90e92c34718a8f5a0643d60160f5602aa4524b0f54064a3eb0e08fa92c3d48192f340323cd0098f5092cabe9880f1234d3468ca48f8314a4ba4b0d1a62a3460ca8f443583cf0d32ae4c38343a4d48f692c3d38d94f4a3643d08d34f3a34c3cd8ca8c06326a5e0c52f3400d3d3c940f4804e3d00100f4d55c3d2bd12e9c643abd9880f103433448c7c8f43143d201c0f3e0403d1c940f44f44abc9880f0e34d3c30d048f23143d0c940f400643cf8138f3cf453cebd10f38c38ba6990eaf46203c28d0cd1031f3430c748f03143cdc942af092c3c3993893462a3c20d38f30358a3fb0e0ae092c3cb8cd8c063322588c50f3400d3ccc940f30f44ba81936e9e641a4b1880ade3143cbc942ea094e3cb24b2af862024d0ca4adc3143c730e0aef250a280c50f1ac3832d80449300083caa4d0f289342ab0020f2b2503ca3d10f269413c924b0f0634d3c10d26e72341a290c50e6001d3278048aaa0083bd3150f023543270040f22c382488c50aa80083c8bd60e86f583c80d50f22f44a279880c9831e3c849428ac6203c78078ae3250b9c25368a292c3ae1924c9662a2401880f143493c70134f1a02a2b8c942cfe94d3baa52689c92c32518a8aa66203c60d24f19250a2aa4b0f1602a3c549428a892c32498a8f1202a32418a0f100703c38160f0c04c3c28100f0801c3c198a0f006483c124d0f026343bf0d90ef23403bd0cd0eee3283c02562e6894c3bf99c0efa664ad49930ef66403bb18d0c763283c024b0aa40083bfa4b2e663403ad80f4aa20083bf2524efa92cb990d00eb403d2a80020ef8c383bda4b0cb001131c0040a9e0083bd3150ef295431b8040ec69493bc24b0cae01131b0040a9c0083bba524eec92c3ac80f4cac01131a8040a9a0083babd10ee66643b89960edc64c3b59908ed46403b418d0caa3292a60c50ee06643b398d0eeb250b9e2538ee46643b79962e7c64eb9b9930ed86403b318d0ca83292a58c50ee955c3b9bd10ee492cb9d8d08e5e02b2ac8024a940083b8bd10ee092d3b7a4b2e7434239700ace4e0272ac0024a920083b73d10edac383b624b0ca40112a40020ed72503b53d10ed292c3288044a8e0083b43d10ece92d3b324b0e5a02b393009cca00112ab8024a8c0083b298d0c66010bb04942ec6c4d3b230e0ec69363b024b0ec46363b098d2e5834daa08c50e5802931a004ac680112a08020c6431c3188040ec0c543180c70ebe0103ae3d1288e92c31618a8eb03423aa8ca8ebc0113ae8040eb9250a2424b0c5662a3aa0ca8eb66703ad1990eb26343148ca0ea20283a9807288c620a229882a7e3143ac49428883143140048eae92caaf1880ea834d24d0ca4a78314aa00c50eaec383ab18d8ea434d29d8c50eac3143aac940ea8c383a99928ea46203a88d2aaba314b10807ac420123a23d10a726203a80130e9e0403a701c0e9a0643a60190e960403a1b0e0a70314a378c50e943583a549428ea3143a40d30adaf4439b25068da92c39298f49066203a48d34e8e34c3a30d04e8a32a3a4c9428e86203a43d14e8ef442b624b0e84343b948cfead6315a398c50e62043313804c9040083a349428e46203a2c9428d0314a370c50e86f582b6bd10cfe9413a024f68d892c29b9880e8803d3a1bd128a66203a10100e8263c3a0a530e6a9402d39900e832503a03d10e7a94239f1908e6e6403120ca4a663143a04940e7e64e39fa4b0a640083133d30e7cf4839e98f0e7834839f4940e7b25039e4942a8a31439d8190e7404039c3d10b52c3e2d3b0f4e6ec3c39b30e0e6a632aa19880e6833e3110c74a6231439c98d0e71250a381880e6ef442bfa4b0e6d250aa21880e6b25039a4942a843143998190e640403988100e606283978dc0e5c3643968ca0e58c5430f8040e443703850d30df033436c0ca0e5601039099c0e1265837b9900dae6343950070e403703840d30de23343680ca0e5206438f8dc0e0e34c3780cd0d9e32838e9992e066583819900dcc628b918d36a5831439180d4a5800838e0dc0e283643808d30dc23343518ca0e5001038d8dc0e263643800d30dc03343510ca0e4e66439318d0e3407037f8130dbe03435f80a0d8001c38c81c0e2406437f0100dbc02835f0070dfa34c36e8cd0d3c328392bd128cc92c37e0d30db833435e8ca8d3a328392c9428ce92c37d8d00db633435e0ca8d383283920040df404036d00a0d7401cb8f19c2e0c664b7618d2d9831c37c8130db203435c80a0e4601c38f99368ca62038d8d34a56314391006aad2621a321880c3831f2950c50e4201b3904940e3ef4438f0cf6a6c31430d8134e320412948020e3c64da979880e3a364b828d62e2e340b888cd2dd6328b658046d880102940020e3925038dbd10c3634d38d0d24e32341a268c50c3201238c49428c062038a8d3cc3031f2930c50a4a0083898d34a4831438c49428be62030b8c7ca463142910020c2c04d3890104a4200838b8d92e0635838b0d02e20334b748ca2d92011b610040a4000838ad570e29250389bd10c2c34d3890d0689631430a0048a3c31428e8c50a380083888d92e043583880d00e18334b740ca2d90011b580040a3600828d0c528bc6203098c7ca3231428c0020e1e3643870d60e1a3403860cd0e16328b640046d6001028b8020e0e64da319880e0034d37e8cd4a2a314385006aad0621a311880df83353088c7ca28314384806ce11250383bd10e0c33da9a8c50c2004d37f0104df40292898020e0c64da971880e0a3643820d60e063403810cd2dd432837c80d6d94011b618040a24008380c940e00f443080d34dfe34937f0d068983143070048dfaf4537e3d10df692c37d0d0cdf233fab38c568c231437aa534de692c37819368ba6203700d34dba3352880c50df001a37924b0dca62bab318868b862036e0cd4c1a31f2878c50dee01b37b4940deaf443720d34de83493778d04dc431da2d8c50de6f453793d10ddc64337698feaca621a2d1880de32503783d10dc864d3779904ddc6203760cf6a683143060134dbc04136d00a4a1c008376a4b0dd864da969880dd63643750d60dd23403740cd0dce32a3730ca0db2035b638046d820102868020dcb2503722538dc692c371193aac6314370c940dc0f443060d34dbe34936f0d068943143050048dbaf4536e3d10db692c36d0d0cdb233fab20c568b23143679960db0018368a4b2ac262035e8d069343293048c74a1631436b8064dac6483630d20a1400836b2560daa67036a1990da664c3641900da46343670d62d5c01c368c940d9a64e3629928d763353030c74a123143660d20da1250367bd10d9c33d3668c50c1004d35f0104d740292840020d986583658dc0d943643648d30d903403638cd2d5c0103631934d8a6203620d90d863583610d00d603343608ca0d720353570044d5a0102838020d806543040d60d7e35435f0d30c0a01035ec940d78c3835d9880d7434e35c8d2aac031435a9934d506203510d34d3c3352828c50d7001a3561884d4e62034e8cd4c1231f2820c50d6e01b35b4940d6af4435a0cf4d563143040134d4004134d80a4a0600835a1934d546203598d90d643583588d00d603343578ca0d340353570044d5a0102810020d592503559938d5464a34c8cd4c0c31d2808c50d5204ea530048d50f45353bd10d3e34334c0ca4a00314353010cd4a03f352004cd472503513d10c1034d3508d24d4034134f8c50c0a01234f3d14d3af4434e24b0d3634334d0cfcd3231534c0c50d2e070b268d00c9a058b2d0cd69f631432d01349f600834b30e0d2a63634a18c4cec620b498cda9f431434980d89f400834930e29f231427c8020d06640348b0e0cea314a7c0020c9834cb47c9429fa620b474940ce66203480102cfec583251960d1e0303470060ce4c38a7ba4b2bf46262fd18949ee6203458cc4d0e325a4d0c52d16031b4380649340083249960d1a0343460070d17250a7e24b0d1404e34481c0d1004c343c940ce292c3241938d0c04033f24f0cfa93c3428130d08034b2d8040d06c543413d10cfec38a7a98809e631434149428e26203408100d0002833fc9429ec62033f3132c8c64c30498a0c1031c33f4940cfac38a7a0c509e4008b228cd0cf834033d80a2c8864030398a0cf4034b3c0070cf0010b3e4940cf8c38b3d993acf464a33d98d8cf46322ad9882c86336b3c8caa9e23143218138cf202aafc8038bf200d278802093232433c00d0cee01cb2018d0c8034c33380a0cec934b3a98d0cea33433a00d0ccc028b20a500cca3343398090ce5250a1024b0c7e64eafb9898bec62520f9882ce034e3358cd4cc8334b2f8ca4cbc31d24d0c50ce202524c8022c7c63433780c0cd2028338494283a3143378d00cd033433700d0cda0283360072cd7250335b0e2c7a636b3518aa83862031e8d38cd432aafa8c68bea31920e0c52cd204eb340128cd203633400cacc001eb2e8074cc001232e8046ccaf45b323d10cce94333324fccca92d33224b2cc6643b3118fccc662b331189ec4a343b0f0cfecb232bb168c9ecc231fa7f8c5683631432c810cc5a03f31280acc3c027330807cbf800f27f802483600833000d0cbf25032f30e2c7863632e80a4cb801d3160d50cb601c32a9950cb4654b132560ca86543158d20ca66543150d20cb202832c0d00cae33432b0ca0c5204832ac940ca8c383299880ca43403288cd0ca032827f0020c96c383239924c84620b190cd8c94c383209882c6033632798a0c9c02832624b0c9a3493200c50c620283263130c60334325c940c94f44b049924c8c63d31f9880c7634ab110d069d431432480f4c9000d323c940c8cc383221880c8a33631d012ac5e036b1080469d2008b040d50c5e0343028042c0e6543221920c860283214940c82f443202504c7e92c31c8d2ac403413170caa83c31431f0104c7a01d31e0044c7692c31d0cf4c7231431c00d0c6e02a31b00a0c6a01c31a3152c3e04cb194942c60f44b19a528c6694931924b0c626403181882c0a049b1780f4c0a0253178064c5c0083159960c5465831680d0c59250315b0e0c546203148d2a9d031431400dac420123140160c4c94c3121920c446403138130c4d250a4f8c50c4234031198f0c4063431280a0c492503119880c452503108c94c4031430f8138c3e02830e0dc0c2e3643088d60c1a3403048ca0c3607030b0190c2004030600a0c1001c30d0dc0c2a3643090d60c1e34c3058cd0c0e32830f00d0c3a01030c81c0c280643070100c140283028040c3925030d9938c34620a780c50c3204e30c5570c2f25030b1938c2a620a770c50c2804e309c940c24620a768c50c232503081938c1e620a778c50c1c04e306c940c1864e30598829d83143050138c132503041938c0e6203030c50c0a04e2f58192bb2058ade8130bb20402c900d0b7a0282c918d2bae664ade1960bac64c2c899029c6c38afd24d8bf4935271a4b0be46652f49992bc2659aea9960bc264d2ea9930b366412c81900b006203020c78c06319b02007ac060193024940be2064af10162b8404eadc8130bc00402cd00d0c072503010190c020583000138bfe04c2ff0100bfa0342f40dc2ba2364ad48d30ba03402c60cd0bce370ae90d90b9e3582d38d00b163342f28dc2b9c364ad30d60b9a34c2c50d00bc8370ae60d92b483582e60d30b483402c48cd0bf80342fd8040bc6070ae58192b460582e50130b100282e48d30b443402c38cd0bf4f442fba4b0b9034c2dd8d08b423402c30cd0bf52502fb24b0b8e3402c28cd0b8c0402cf80d0b080282e28130b3c0402c180d0b8834c2ce8d00b043342fc80d0bf00102fbc940becc382e18d00b743362ce0cd0b023282fa80a4be80112f98042bbe364adb8d60bbe34c2db8d00b323342f94942bbc358ae08d3ab6c34c2ee8d00b303342f88042bd52502f530e29c26202f30c7c9c2314a700c50be09582f7a530bdc9402f698a0bd92602f598a29be6202f55570bd2f44af3990e9bc6202f40d0cbca31f26e8c50bd092c2f3c9429b83142f18048bcd868af2c940bcac382f21882bc634e2f180d8bc2f442ef0d92bb83582df8d08b603402cb8cd0bc40102f0c940bba3642ee0d62b8034eada0d30b2c3342f00040bbf55c2ef3d10bba92caee3d10bb892c2edbd10bacc382e48c7499a3142ed3d10bb0c432ebb0e4baac382e898de9ac6202e78cdcb9c31f2e40c749983142edbd14bb4f442ea30e0ba6643a6d1880bb26282ec49429b23142ebc9429b06202eb3d14baaf442ea30e0ba4643a6b9880ba03432e68c7cb8e31d2658c50ba6c382e924b0b960112650020ba32502e824b0b9f250a6a8c50b940122e74940b9ac382e61880b9634e2e500d8b92f452e43d10b8e92c2e30d0cb8a33f2e20c54b863142e08dc0b803642df8d60b2a3342e10040b832502e04940b7f2502df3d10b78c382d498d69a46202d38cd4b7631d2640c50b7d250a6a1880b7a6282de49429a66202ddc940b743142dc3d10b6c3642da0d60b6034c2ca0cd0b720102dc4940b6a3642d98d60b6434e2d88d30b5e3402c98cd0b6f55c2db3d10b6a92c2da3d10b6692c2d924b2b62f442d8a4b0b60f442d7a4b0b58c382d10c7498c3142d6b0e4b56c382d498de99e6202d38cdcb4c31f2d08c7498a3142d718a0b5b250a689880b58f452d5bd10b54643a681880b503432d28c7cb4031d2620c50b5492c2d180449860082d4c940b5092c2d3c94299c3142d34940b4ac382d21880b4634e2d13d14b42f442d024b0b3e3432cf0cfcb3a3152ce0c50b372502cc0d92b2e358aca8d3ab2834c2cb0d00b340102ccd572b30f442cc24b0b2ef442cb24b0b2b2502ca3d10b2692c2c918a2b23250a609882b0e31e2c8bd14b20f44ac7a50cb1a92cac5990e9806202c60d0cb1431fac30c78b0a31d25f8c50b1f2502c7193ab1af442c6a4b0b1892c2c5c94297c3142c4004ab152502c530e0b12620ac40d38b100362c3bd14b0cf442c2a4b0b083432c18cfcb043152c08c50b012502bf8030afc01c2b9b0e0afa0282be00a0ae4f44a1da4b0af60642bd0160af20422bc00a8ae2f442bb8108a706582bb0c7287e620a1f18809f431e27c8d009f031c27c8cd687a31429ba53096264c2ba8c60aeb250a211880ae80402a9a5609786582b98062878c3827ba4d89c693225518d893c6322b80c94ada3192b90094ae20192b8494288292c2b78138adc02a2b6c94288092c2b60100a886582b581908d001c27b19609ea6582a19930ad43542670d3093e01c2b530e07643142b4a5c0ad09642b32500ac26282b39990ac86342b00c70ad2c38a939880a6c3362978cc89e031e25800d895201e2b430e0ace64da889880a6a3362970cc89de31e25780d895001ea8f98809dc31ea8b18809da31e2b330e0aca92c2b21936a1862029a0cd8a5a3322b18ca89d831e25700d8ac402a2538078ac2c382b00d36a0c31425680d894c0122799930a6264027518a0abe34824e8c90abf250a9f18809d631e2af18a09d03282ae8c70a8035829f8d30abd2502a01938aba335a9d0c509ce93427124c275a6341d60ca0ab8318aae4940ab8c38a9e98da75462029e8d387543142ad80a4ab40282ac99c0ab06642ab98d09fc32829c3134aa6c3827b1934a98649a16188094a31e2ab2520aacc582aa3130aaa628248bd10aa893ea168c509012502a9bd109ea64d2a59924a86641a17988094831e2a90d20aa46582a11930aa23702a80d90a9e3402a70cd0a9a3282a64940a96c382a29938a943642a48d60a903402a38cd0a8c32824fc960a8a3482a2494099cf4a2383d10a8692c2a10cfaa603142518048a82c542a00d60a7e34ca731962a6064c9d58c70a7c05429e803285492c29e18a8a74628a148c50a78c3829d9880a7431429c3d60906f4429bb0e09e664129998f4a62635a1c9880a7203d29c3d1285c31429bc94287462029b0dc0a6a36429a0ca0a672502990d38a632502980c509cc64029818d0a566702921990a3a65828a9930a2063428298a286e92c2951990a4665828a1930a1e63428598a8a086282948dc0a423642850d60a3834c2898d00a1c3282840c70a5e6702971990a5a6342940dc0a4036428d8d60a2434c2868cd0a0e3282960c70a4e67028f9990a2c6582889930a1863428318a0a56f452953d10a523432940cfca4e315a1b0c50a4d250292bd3ca48f45291bd10a4434f2908d0ca4033f28f8c5686831428f4940a3af442850d34a3834128d8cf686631428d3d14a32f4428c0d0ca2e33f28b0c5686431428abd14a28f442898d0ca2433f2888c5686a3142883d14a1ef442870d0ca1a33f2860c56862314285c940a1464e2849880a1034e2838d28a0c314282bd14a08f442818d0ca0433f2808c54a0031427f80d093e65827f0d509ec95827e80909eef44279a50884092c275190a9ce6202728c9693431427e00949f665427d24d09f263427c0cd09ef25027aa53883e92c273988097634e2720c9493431427a19208e325027b3d109ea92ca730c5076404927a25609e463027580f09e72502730c509e49402748d009e203424f99609e03702778d909dc34c2768d009d83342740cc09d603c27549409d232520f0c509d0640a73c9409cec38a7319389cc6361e198809cb25027230e080a04e26f99c09b0664269996099a64c2631900982634271bd129c492c26f19909ae65826619309906422629900980634271c9409c492c26e99909ac658269193899e64c265990097e63426e0dc09aa3642670d309943402618cd097c328a7149409c4c3826d9992992658a63993a98464c264990098e63626118d097a628270d5709c0f5b26fbd149bcf4426ea4b09b834326d8c509b525026cbd3c9b0f4526bbd109ac92c26a8d0e99231426a49409a6f4426924b099c341a638c509a2f452683d1099e92c2670d0e984314266bd14998f44265a4b09943432648c509912502638c5098cf45262bd1098892c2618d0c984314260bd14980f4425fa4b097c34325e8c50978c3825e3d1284862025d8c7897692c2008c509743402598ca0970034259007096e02825a80d093e02825a0070974c3825ca4b097064da11988096e33625b0ca896a31e24f8ca096831c259a4b093e34d2590d06844314258b0e284e620258c9428506202580dc095e3642570ca095a01025600f0956328255c94284a3142528d60954f449d618809552509d6988094834e25181309523702540d9094e334253004079b250252bd1094892c25181067560082508ca09403282048ca093e058251013093e3582510d3094325025030e093e64e1d5188081231424c806093cf4424ea508936342a4d0c7893d25024e0d3893431e24ec94093892c2028020937250a4d4940934c3824c9880902c38248b134900c38238193682a6201e68c7893001e22a250682492c24b80a88fef44220a4b092c0421e1006885000823f3d1282092c1e598a892a04224a00a87840262454940834620249819092401e2454940912c38229993492064922798d682e6202478d2492200e2484940910c38237193891f250a0c988091c92c2468cac87c31520c0c5078200f24630e087a31424580c478000d244bd6089c941a0a24b07ca6412438c9890631a2450034912f44244192482e620243c94090c0642428138908040241c94082c62024101008d894d20a24b081064d240809890001a21e24b482692c1e518ac77c62723d8c9c8ee31b23f809c8fc01b23e803c82492c23e00a88f725021da4b08f406423c81388f004023bc94082292c23b01008ea06422049408dac38233992682c6201fe0d248e805923981608e404d2388038881250229b1348d8c3821d18808d434923800388de948237b1608dc354236c9408d8f4423318f48726202348d247f633d23581208d635823549408d2c3821c188080634e1e48c7880a04e23400208ca67023199908ba634233253486e92c23219908c465822f99008b863422b8c708cf25023330e08c235822c8ca08ca92d23224b089a32b21b0c507c602b1ec809c790013231a4b48c492c2308d0489832b21a8c507c402b1ec009c78e01323030e08be92c2258cac8683142198c508bc92c2190c508ba92d22e24b08b662b22d18808b23412250cac8623141f080ac7ae02722c007c78c01322ba4b0860008229bd6089ec5822b00f08a2f4422730e0890631217988089233d1eb0cc477a31922a80f48a8031229bd1085c31422918d08a325022398c482a620228013889ef442168c5089d250216188089a3702260d9089634c2250ca0893250215988088a658224250485492c224494088ec382220d3888d250222bd108883292148c508860491fd00f48749582140d6088400c21e3d1085e94221524f878a6291de18948483422100c68882025220003485c65821698d087e05421f24d087a634216250087925021ca53886e94a1e218a47766252138d3883e31a21d809682d25021d3d1085c94d21ca4b08703491fc0cf486ec3821b199086a65821a190086663621918d08626282180c7085f250217313882ac38216a53885892c2158cc47aa32520f00388552502149938850f44213a4b084c04921280a084925021180d084402821080d084125020fb0e083c6361e1988080234e20e813883802920d80a0835250a0bbd1082e92ca0c8d247ee33d20c81267ee02520c18a282925020bb1387b6635a000cd482c01a20a8038828f45209bd107fe6431fb18fe7b83439ea0cfc81e31f2068c6c82403f208806c82000fa07c94081ec38a07192081c630a06c94081ac381fe993a7546209fe8cd8754314a06013881803620580a48140282048020810c3820399248006202043d1080c6491ff988080f25020330e080864e2028d3880b2542020d20806054201015080200c2003d107fe92c1ff01247fa00d1fb98807e83341fda5347ec92c1f98cd07d432a1fe49407f6c381fc18807e00281f780a07f46581f700d07f201c1fc25607d83341f40ca07eec4d1fb30e07ea3361f58ca07ea3141fa24b47e692c1f918ac7e26201f80d047de32b1f70c9c7da31f1f60c547d63141e9809c77400f1f530e07d26201f40c507640191dc80347ce03c1f2b0e07c063d1ee18807cc03d1f2c9407be6311ed98807c8c541f18dc07c43641f08ca07c12501efb0e07bc34e1ee80f07b92501eda4b07b40311e90d607ac9411ea24b07a032a1ec99c07b06641eb98d07ad2501ea98807aa9401e78ca07a92501e88d387a63341e93d107a23141e8494079e3141e7009079a00c1e53d1078a6201dc0c687980251e580347952501e2188076e31a1e481507903701e38d9078c3341d5009078b2501e230e07860191da8d6077cf441dea50877892c1dc18a875e3421d68c5078400d1e0a4d07806341df80d077d2501dda4b076e62a1da0d387583141dec9407560081de4940776c381d98d3875c3361dd0cd07723281d881607640101dc494076ec381d8013876d2501dabd1076892c1d98c507640491d880f47600121d7c94075c3141d6c940758c381d598d875400d1d481c27232501c8b0e26e663589318806e634d1568c7c24c3141d4019474e0649d3007874c0121d281222486201d28d606e034c1d2007a7392501cdb0e263e64f8e998862466201ba0d3863c3361d1807874492c9d08cae3a23158908c5074202b155004c48000f0e880242420081d030e073e3371540cd63a03158900c5054e013153004839e0081cebd6263a9599b7250623e92c1b7196463a64108f988072c31a9cb009873c00c1c8c94073af449961934738649990190e3a8621892988063634d1cd8d246d83431b58d0454a31f08e8c527252501510c742383141cd019073204e1cc010072e0121cb494672725099a193e5ea64b8ed98862566201ca813872801e98e253639c92d88f24b06cc64d15098ac47c6270e618842346201c68c9c70831b1c9809872401a1c8803a39692d88ca4b054062b11e989c39662108c98807183271c18c6e7060279c6006c72000f8eca4b625292c1b1993453e62b08c188071e02a1c7007871b2511c6494266094f8eba4b06c464f14e18ac53662908b98807160651c5019071204f1c4013870e0411c3010070a01e11d806a2ae0081c24944707250998a53e5e894b8ec24b625092c1b0993c53462b0e5188070404f1c0813870002b1bf80a84760260a580206f2c551b430e068c3490d58c506fc0360eac9406e4c4d1b7b0e46cec38983993669463787e188068a34917f8cdc5e033313b8c7c4da31e0d80c542543141be81346f80371bd80d86f401e0eac940658c4d1bc312c6dcc391b330e251e64d1aa992669063787d18805fc3371778ccc4ec31f1360c7835e3150d50c506ee9481b6a4b03520081bcd5706f12501bbb1606e2c4c16925306ec6281b00d646bc3559840d346ea32987e8c505f6035135804835000817ec9606d892c1ba015034e0081b9c9405a4f491b93d106e293e1b5a4b260c34d1a48ca61f63141b801284ea013135004834c0081b7d5706dd2501b6b168636c581b631386d6c4c94a19646a8655985193469063588018805f43351348c7834a3141b501586d20541b449446cf2501b33d106be64f94999346ba64b1a9992661c643984990637062187f988068833d13a0c7c4d031e11d0c6c35c3150d20c506ca04b1b201246c603d1b1006c6c200f1b025246be92c1ae0d2068603d0d180206bcc551aeb0e06b865898019306b63701ad0d923e034c1ac8d006b03361ab8cd06ac3281a101244e001d13080703440081aac9406a8c391a9b0e261664e1a90d906a23589868d3a60834c1a80d0069e3361a70cd069a32817c80dc5dc033137807435a0090d0802269555c9a44940524c589a63158698c551a5b15260cc4c1a530e060c9581a4a53069092c9390d665ee34d8cf0c504e403517b80a44dc013130004a4c001112f804033c00887b24b068034019e8caa36c92d87aa4b068864d12f18ac33662019e0caa33a62019d010067e03419c007866e01c1a3807068d2511a2c940688c381a1993c68464b8da98861e662012e0c7867c03619b0078682c381a024b067433519f8ca63683158790c5067c04d12d804c33200819eb0e4678c3819d98dc67463619c988067033719b8cda36631419b01345ec03792a007c25801d92a004c330008197bd64658f58193bd10640c5918eb0e263065914a190461463588798805fc3591760cc432a31419a80f066801a194bd1464cf4418e30e062e643149990462a63f18898f461c63718498d638c62188718805d633112d0c7c47231b0cb8c5432831419980fc66403d198806c66000f197c940656c481970d56224314196c940658f4418da4b052434d1830ca61fc31412c804c326008195bd6062c3411950cd460a3298888c5065355c88a988065004c193c94464d2500e4b0e063264f979992c6066358e4188622862017e0d3c5d433112c0c7c23631419281386480411918100644035190807864125017eb16063e3558880c5063c05418ec94463925018db138392c3818c193e5e464b14798d46206318e3988622662017d0d3c4ae31f0c90c5263355c98c4940524c5818d3150632c3818c24b25d234992b0cd65f03298c88c504ac05917c01345d20250c8802062f55c18b31586283311898cc238a31418ad570628641189990060463518098d23886201890d683dc334188c940620c3818618d861e34e1868cd8608334128007431e00818755704aac40186b0f06183308d00c5061603c1854944613250184312c60ec38183253860a94b0f824c83dc93118224c060692c97c0d3e5da34b1810c9c6023268d60c5633e31417b813c600032127804c49c0110c700205ff55c17f49405fac5817e30e05f695617d24b04ac35917c8d545f034d1390cd45ee32987c8c5049a0120cb00221e862017b00785e495988524b05de65917619043186201738dc05c036416c8d605a234c1658cd058432a15a8ca05ea0268e0a4b621292c175990449862b0c598805cc36416f8d605a034c1650cd058232a15a0ca05e8027179d5705e525097419263206201258d645da34d1748cd431431417281c05ba06415f81605b004c167810058e02815d807857401c974256631292c97219c259c66496e19325ae64096318d05d034195c8c7657031c0c48c505c807016e01905ae058167013058c03415c80a857002817880705e155c177c94049665917719545da64d87c188049231e17181c05b6064169013059a04016200a056e01e15780705d9251175c9405d4c38174993c5d064b8e01886210620166010058602815b007855c01c173bd145ccf441728d0c5c833f8df8c5620e314171810c4900130c380205c5250170bd3c5c0f4516fbd105bc34f16e8d0c5b833f8de8c5620a31416d810c48e0130c300205b525016cbd1057e34d16c0d045ae33d8820c505a4041123004c30a00816b3d145aaf4416a0d0c5a633f8de0c56206314169010c48a0130c200205a2f451683d1059e3431670cfe37c3158830c5059a04316600a44880130c18020596f451653d10592643164188058e3431630cfc58a31f8dd8c56204314162010c586029121804c3040081614944583250160193c57e64e15f192c57a62115e188057634f15d0d3857234b15c0d2a3743158dc8c5056e04f15b00d448401f0960074484013120804430200815abd14568f441598d0c56433f1588c54560314157810c55c029120804c300008156d57254b250152b0e05306591491960558655155995050462092c8d664ea3359350cd22ee31412c81644ea04d13501302ee00815524d055263515418d05026209538cd654c3348bb0c5054e03515300d02ec008950d57054af5a94a256852c941147a50050092c93b19064d86408bc98804d235a12b8d0646a31a0ba8c505480261518090544018150c94454125094ca53e52694e947252c51292d13fa4b24b464f926192e2fe6218bc18804e834f1340d384bc34b11c0c6e46831a1198c642fc3150ba0c5053e04b14f009c53a02514e006c53601914d003c25800814cd570530f5a14bbd1052cc3814a996a51a65614618c451663014418822e6314132816a46400e0b80020529251149c940524c4e148b12c520c38147a4b24ac34f9258d2e2fa3158b90c504e404f128804c2de008147557051a95a1462504516940143a4b051465a9398d064cc3401210c7448231c8b88c504c805a12981044a801d91880382dc008944d570512f44944256a50e956144250850e93e931990a2da6201318d6a46031a1180c642da314943016850c04214280d4508034941807450601194049464ff250141313c502c4b14030e44fec38929193e49464b93898de4c463692e98ce2f862187018804e234f1310d384ba34b1290cdc49433311b8c6e45e31a1178c642f83150700c524fc04f93e813a4f804b13f00dc4fa03613e00cc4f602913d00a24f201f93c00744f201313c004425800813bd5704ed25012cb1644eac4d13a30e24a265992a996248465513999244e463613898824a23591380d584de3549278d344dc3379300cda2d431412e012049a03612480c82f6008136c9404d8f44135a52c4d4941134a4b44d092c1338d2e4823491330cf44ca32b1320c9c4c63151310c504c204a92701044c002b12f80aa2d200812f3d104ba92c8b418804b835812d810a4a801e12d55704b2f5a12c3d104aec3812b19684a264112a99004a863d12998c44a46201288d044a033c1278cd449c3348b60c5049a05a11b00382f4008126557049695a12524b22d66201248d68490070123819048c05a122816048804c12180d048401e120807045007090c819040e058902813043204010280d03cc02812024d044e07090c019240805810c013040804011f80d03ca02891f55722c892c91a98a844c37090e8d9241235a8fb8d6042c34c1018d003c833411f494447b25091ca53e2c692c11d193c47062b91a18a84666290b1188045a3651128d9244235990e0d6241c34f9040d3a3fc34d8fb0d3044034110a8d003d63350f18cd03b831411e004847600d11d30e044807090981923e004c10901004020360f780d03c002811cd5722c262011b0c7844607090a019240405a8f8816042204c0f700d03be02891c5570470f4411ba4b246c65a11b0d08444070908019240005a8f6816042004c10001083da0400ef00d046b25111a4940466c38119193c46264b118188445e62010781003fe0360f600d03ba02811761a245b250116b0e243e058906813a3f804c10f810041a0360fe00d03d4028116557445755c9153d6e452f579133d1644af44115256c452957114250c44e93f11324b444a92c9118d0e44832b8af8c5044804311180ac4440130af802044325011030e043e06410f016241804e8fd81304140360fc00d03d202810ebd14438f4410db10c434c3810ca50c43093f10ba4dc42c92d10aa4b04283431098cae2bc314109010c42202b108004c41e0110ad802041d55c10681c0418064105816a3f405810501303d0028104c944411250103b13840cc38102a53840894a101a4b040434f0f80ca62ba314100813c3dc029100004c3fe0110ad00203fd2500feb0e03f80640fd81603f404e0fc81303f00400f380a03eef450fb3d103ea9430fa24fc3e692d0f924b03e23430f80cae2b83140f7810c3dc02b0f6804c3d80110ac80223d72500f5b0e03d40648f481623d004e8f381303d20400f400d83ce0348f23d163c6f440f3250c3ca93f0f224b43c692c8f1190c3c462b0f098823be3438f00cae2b03140f0010c3be02b0ef004e3ba0120ee80442b00088ee49403b8c380ea3d64398f440e3a5661da92c0d799643546580ca990831863e0bc98a82c86260ab8d6029a3420a18ca83b60260d800383b400c0e73d14396f440dc250c36c93f8d924b61d892c0cb990c3286420c598f82fe62b0bc18a82c66260a60d0828e33f0a10ca827a3270998c983b203f0ec009c3ae0190eb003c3aa00d0ea49403a665587798803263580d38d3834c34c0bb8c783a40540e8a4d03a0635877188039e3340bb0c7839d55c878a4b034a65a0c919002ea62a0a58d002643260e680303992510e5c94038c94f0e0a52c36492d87824b035c64f0d2193833664a0bf18ac2e862a0b118982ac34e0aa0d2c28232a09e0c9c2623260e5006439200d0e4557038f2500e330e03806498c6988038a35a0be8d642e43580e20d5834034e0d60d3433e34c0c88cd83143320b60c782c231a0e181543840540a981242940360a00078382f440e0256631092c0df99c037c6640de99303786400dd98d03203420c48cf82d632a0dd0c7437231c0a4810827e02a0dc557036a6318ce188033c35a0b78d0031c3340b50c782d231c0db80f02600180db557036a9418cd24b036865a0ce8d682d032a0d98c7236555c0d93d1231a95a8c4255a3389428cd24f833865a0cd195831a6420c418f82ce62a8b398a42cc6280b0189029034289a0caa13c32809d8c9629005a09a007813c01c89d80642f800e8be003436200c0d8557035f2500d730e02fa6590d6995435864d874188032c3360bd8c783572510954940354f440d4a53c32694d0d4252c34e9430d3250434a92d0d224b034634f0b90d3434434b0d08d243403430cf8d0433c32b0ce8c9c3383158738c5028c02709f004827400f0cdb0e033462187318803323360cc0c7832f55c875988032c35a0bd0c7825e01a0cac9443292500c9b138236c380c924b032234f0c80d2c2de3350c78cc431c3290c68c561d43140a9012c27200f0c649443172500c5193c31264b0c418861d26200c38d9030c3580c28d3830834c0c18d003043280c08c7830031c0bfd5702fcf440bea5682f892c8b398802f635a0bd0d082f32510bc49402eec4f0bb312c2eac390ba30e02e664f0b919382e264b0b818dc2de6360b718cc2da62107018802d834f0b58d2c2d43370b48cd82d03330b38c542cc3140aa81382a204b0a280cc26c01b0b2806426c00f09600202c92510b1c9402c4c380b0993c2c06200af8d902bc3580ae8d382b834c0ad8d002b43360ac8cd02b03280abbd102ac92c8718c502aa0120aa3d102a695987124b02a46420a898a82a00340a780a829c01c0a6c9442992500a5a4b029434f0a48d2c2903158728c5028f55c87224b028c65a0a298a82703260a200702872510a14940282c380a00d3c27e34b89a0c5613c31409f013827b55c09e3d1027692c09d196827264209b18a827033e09b816826c01d09a8070268008099c940264c39098b0e02606360978cdc25c04e09680d8258012092b13423ec3908d30e022664d08018dc1ec63307898861ba62006c8d341903370600ccc16c31f0578c6c25601a095003823cc3908cb0e01fe63707a98cc1e062186e188018e33705f8ccc16a31f0570c6c252033094006c24e00f093494024af4408ea4b01fc34d0920d2c2463490880d0c1f63290778c541be31409101241a603d056803c2426280900ca41dc31506f0c5015800f08fc94423d25008eb13821e64f085192c1f463507698841ba6200690d2c18c3350558c6c23801a08d8038234f4508cbd1021c64308498fc1d862106e18801b03430688cfc16831f0550c6c23003f08b806c22c00f08ac944229250089bd1022494f07f253422294b088250c21e92d08724b021033d07c8cac1e83270758c541d4314086813c21804b08581241ac04306800f418a02b05f009c166013054803c214c39084b0e021064d07c18dc1d26200838d9020c3580828d002083360818cd020432806200dc17a033059007c20201008049441ff25007f31381fac4b07e30e01f694e07d24b01f234f07c0d2c1e63250740c541ce314067812c1ee03105e009415000f05380341ed25107ac9401e864f07998d41cc6200790d3819c04b078c9441e1250077b13c1dcc4b076b0e41d8c38075993c1d464e07499281d063707398d81cc63206a8d3c19a34b0610cdc1763330588c7c16031d0530c641ca04e072012c1c603607100cc1c200f070003a1baf4586e3d101be94306f24fc1ba92d06e24b01a83430660cfc18232b05d0c9e18204385d00fe1a802b866009c1b601306d003c1b2f4406c24b01ae34906b0d0c1aa31506a0c501a6c4d06930e41a2c38068193419e63706718cc19a62106618801723330528c6c19603606500a019201e064494418f25006324b018a34f0620d2c1863310610c54182314060494417f25005f193c17a64b05e18d417662105d188017234b0520c6c17004e05b807816d25105ac940168c380598d3c16434b0588c54160314051803815f251057494015ac4f056312c156c3905530e015264f05418dc14e636053188014a34b0520ccc14631e051013c14204e05000dc13e03604f002013b25104e494212af4404aa4b213634f83b0d3613434b84c8d260e43438440cae10e32981b8c5603831404d813c0ec04d04d012c132049044010c10e04103900ac0b4013026003c06e00900e002013062884b8ca606c31580d8c5012e02902c804c09600f01b002403600804b494612525004ab13a0f264f834192e11663581c988603c6200430d3c10034b0388cd40b031f0250c6c06a31500d0c5012801a0498038124f45048bd120f064383398fe07062180e988010a34303f8cfc0ae31f0248c6c06831500c8c5012003f047806c11c00f046c944119250045bd1011494f03b253411294b044250c10e94104324b410a92c0420d3e0aa34d0418d2c1043498360d0e0d63410408cae0fc3278188c5602c31403e00f40d402b032009c0a2013028004809000f017002405a00804030e40fec3803f18dc0fa633818188602a62003e0d340d23370278c7c05831403d80d80f401e03cc9440f125003bb13c0ecc4e03ab12c0e8c39039b0e00e494f038a4b00e034f8330d2c0de33702a8cd40dc3330368cc40d832b0358ca606631580c0c500d404f034812c0c6025027004c08e00f015802405400803449440cf250033193c0ca64b819188602e6200320d3c0c63350268c7c05231403101900c205803001380be04c02f01000ba02802e00780b601c82c49460af25002d313c0b2c4b02c30e40aec3882b193e0aa64e82a192c0ac63702a98d80a863302998840a46208270d3e09a34b8288cde0a03368278cce0503158138c500a204f028013809e04b02700dc09a033023003e08a00e02280340500090138022095251824c940098c4f025b12c094c39024b0e208e64f82418de04c6200240d3c08e3370230c7e08a31e0228c7404c31402201940860648210166082058820013e07e04e81f013607a04c021010408204002000dc07e03601f00d407a03401e00a407602801d002007325101c494006ec4f01b312c06ac3901a30e006664f019192c06263701818cc05e62180a188005c34f0168d3805834a0158cdc0543360148cc805031f0138c7804c31a012813804804b01180d8044033010807804001b00f806803cf4500ebd1003894300da4fc03492d00ca4b003034300b8cfc02c32b00a8c9c0283150098c5002404300880fc02002b007809c01c013006803e014f45804bd10018943005a4fc01492d004a4b200c3438028cfe01032b8038c9e0043158008c5001004300380fc00c02b002809c008013001803c00400900080200000ff 19 6 13 12 1 7)⟩
def c5Bounds : List Bound := [r0,r20,r39,r40,r41,r42,r43,r44,r53,r54,r55,r56,r57,r58,r10,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N0 : treeBlock 0 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N48 : treeBlock 48 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N96 : treeBlock 96 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N144 : treeBlock 144 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N192 : treeBlock 192 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N240 : treeBlock 240 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N288 : treeBlock 288 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N336 : treeBlock 336 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N384 : treeBlock 384 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N432 : treeBlock 432 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N480 : treeBlock 480 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N528 : treeBlock 528 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N576 : treeBlock 576 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N624 : treeBlock 624 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N672 : treeBlock 672 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N720 : treeBlock 720 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N768 : treeBlock 768 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N816 : treeBlock 816 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N864 : treeBlock 864 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N912 : treeBlock 912 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N960 : treeBlock 960 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1008 : treeBlock 1008 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1056 : treeBlock 1056 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1104 : treeBlock 1104 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1152 : treeBlock 1152 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1200 : treeBlock 1200 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1248 : treeBlock 1248 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1296 : treeBlock 1296 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1344 : treeBlock 1344 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1392 : treeBlock 1392 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1440 : treeBlock 1440 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1488 : treeBlock 1488 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1536 : treeBlock 1536 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1584 : treeBlock 1584 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1632 : treeBlock 1632 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1680 : treeBlock 1680 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1728 : treeBlock 1728 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1776 : treeBlock 1776 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1824 : treeBlock 1824 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1872 : treeBlock 1872 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1920 : treeBlock 1920 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N1968 : treeBlock 1968 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N2016 : treeBlock 2016 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N2064 : treeBlock 2064 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N2112 : treeBlock 2112 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N2160 : treeBlock 2160 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N2208 : treeBlock 2208 48 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5N2256 : treeBlock 2256 9 (caseNode c5 c5Bounds)=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B0n96 : treeBlock 0 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 0 48 48 (caseNode c5 c5Bounds) c5N0 c5N48
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B96n96 : treeBlock 96 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 96 48 48 (caseNode c5 c5Bounds) c5N96 c5N144
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B192n96 : treeBlock 192 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 192 48 48 (caseNode c5 c5Bounds) c5N192 c5N240
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B288n96 : treeBlock 288 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 288 48 48 (caseNode c5 c5Bounds) c5N288 c5N336
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B384n96 : treeBlock 384 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 384 48 48 (caseNode c5 c5Bounds) c5N384 c5N432
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B480n96 : treeBlock 480 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 480 48 48 (caseNode c5 c5Bounds) c5N480 c5N528
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B576n96 : treeBlock 576 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 576 48 48 (caseNode c5 c5Bounds) c5N576 c5N624
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B672n96 : treeBlock 672 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 672 48 48 (caseNode c5 c5Bounds) c5N672 c5N720
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B768n96 : treeBlock 768 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 768 48 48 (caseNode c5 c5Bounds) c5N768 c5N816
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B864n96 : treeBlock 864 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 864 48 48 (caseNode c5 c5Bounds) c5N864 c5N912
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B960n96 : treeBlock 960 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 960 48 48 (caseNode c5 c5Bounds) c5N960 c5N1008
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1056n96 : treeBlock 1056 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1056 48 48 (caseNode c5 c5Bounds) c5N1056 c5N1104
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1152n96 : treeBlock 1152 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1152 48 48 (caseNode c5 c5Bounds) c5N1152 c5N1200
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1248n96 : treeBlock 1248 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1248 48 48 (caseNode c5 c5Bounds) c5N1248 c5N1296
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1344n96 : treeBlock 1344 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1344 48 48 (caseNode c5 c5Bounds) c5N1344 c5N1392
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1440n96 : treeBlock 1440 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1440 48 48 (caseNode c5 c5Bounds) c5N1440 c5N1488
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1536n96 : treeBlock 1536 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1536 48 48 (caseNode c5 c5Bounds) c5N1536 c5N1584
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1632n96 : treeBlock 1632 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1632 48 48 (caseNode c5 c5Bounds) c5N1632 c5N1680
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1728n96 : treeBlock 1728 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1728 48 48 (caseNode c5 c5Bounds) c5N1728 c5N1776
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1824n96 : treeBlock 1824 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1824 48 48 (caseNode c5 c5Bounds) c5N1824 c5N1872
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1920n96 : treeBlock 1920 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1920 48 48 (caseNode c5 c5Bounds) c5N1920 c5N1968
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B2016n96 : treeBlock 2016 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 2016 48 48 (caseNode c5 c5Bounds) c5N2016 c5N2064
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B2112n96 : treeBlock 2112 96 (caseNode c5 c5Bounds)=true := @treeBlock_merge 2112 48 48 (caseNode c5 c5Bounds) c5N2112 c5N2160
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B2208n57 : treeBlock 2208 57 (caseNode c5 c5Bounds)=true := @treeBlock_merge 2208 48 9 (caseNode c5 c5Bounds) c5N2208 c5N2256
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B0n192 : treeBlock 0 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 0 96 96 (caseNode c5 c5Bounds) c5B0n96 c5B96n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B192n192 : treeBlock 192 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 192 96 96 (caseNode c5 c5Bounds) c5B192n96 c5B288n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B384n192 : treeBlock 384 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 384 96 96 (caseNode c5 c5Bounds) c5B384n96 c5B480n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B576n192 : treeBlock 576 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 576 96 96 (caseNode c5 c5Bounds) c5B576n96 c5B672n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B768n192 : treeBlock 768 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 768 96 96 (caseNode c5 c5Bounds) c5B768n96 c5B864n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B960n192 : treeBlock 960 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 960 96 96 (caseNode c5 c5Bounds) c5B960n96 c5B1056n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1152n192 : treeBlock 1152 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1152 96 96 (caseNode c5 c5Bounds) c5B1152n96 c5B1248n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1344n192 : treeBlock 1344 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1344 96 96 (caseNode c5 c5Bounds) c5B1344n96 c5B1440n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1536n192 : treeBlock 1536 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1536 96 96 (caseNode c5 c5Bounds) c5B1536n96 c5B1632n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1728n192 : treeBlock 1728 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1728 96 96 (caseNode c5 c5Bounds) c5B1728n96 c5B1824n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1920n192 : treeBlock 1920 192 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1920 96 96 (caseNode c5 c5Bounds) c5B1920n96 c5B2016n96
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B2112n153 : treeBlock 2112 153 (caseNode c5 c5Bounds)=true := @treeBlock_merge 2112 96 57 (caseNode c5 c5Bounds) c5B2112n96 c5B2208n57
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B0n384 : treeBlock 0 384 (caseNode c5 c5Bounds)=true := @treeBlock_merge 0 192 192 (caseNode c5 c5Bounds) c5B0n192 c5B192n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B384n384 : treeBlock 384 384 (caseNode c5 c5Bounds)=true := @treeBlock_merge 384 192 192 (caseNode c5 c5Bounds) c5B384n192 c5B576n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B768n384 : treeBlock 768 384 (caseNode c5 c5Bounds)=true := @treeBlock_merge 768 192 192 (caseNode c5 c5Bounds) c5B768n192 c5B960n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1152n384 : treeBlock 1152 384 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1152 192 192 (caseNode c5 c5Bounds) c5B1152n192 c5B1344n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1536n384 : treeBlock 1536 384 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1536 192 192 (caseNode c5 c5Bounds) c5B1536n192 c5B1728n192
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1920n345 : treeBlock 1920 345 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1920 192 153 (caseNode c5 c5Bounds) c5B1920n192 c5B2112n153
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B0n768 : treeBlock 0 768 (caseNode c5 c5Bounds)=true := @treeBlock_merge 0 384 384 (caseNode c5 c5Bounds) c5B0n384 c5B384n384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B768n768 : treeBlock 768 768 (caseNode c5 c5Bounds)=true := @treeBlock_merge 768 384 384 (caseNode c5 c5Bounds) c5B768n384 c5B1152n384
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B1536n729 : treeBlock 1536 729 (caseNode c5 c5Bounds)=true := @treeBlock_merge 1536 384 345 (caseNode c5 c5Bounds) c5B1536n384 c5B1920n345
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B0n1536 : treeBlock 0 1536 (caseNode c5 c5Bounds)=true := @treeBlock_merge 0 768 768 (caseNode c5 c5Bounds) c5B0n768 c5B768n768
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5B0n2265 : treeBlock 0 2265 (caseNode c5 c5Bounds)=true := @treeBlock_merge 0 1536 729 (caseNode c5 c5Bounds) c5B0n1536 c5B1536n729
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5Proof : Holds (caseBound c5) := caseSound c5 c5Bounds (extendKnown (bound:=r0) (extendKnown (bound:=r20) (extendKnown (bound:=r39) (extendKnown (bound:=r40) (extendKnown (bound:=r41) (extendKnown (bound:=r42) (extendKnown (bound:=r43) (extendKnown (bound:=r44) (extendKnown (bound:=r53) (extendKnown (bound:=r54) (extendKnown (bound:=r55) (extendKnown (bound:=r56) (extendKnown (bound:=r57) (extendKnown (bound:=r58) (extendKnown (bound:=r10) (extendKnown (bound:=r59) (extendKnown (bound:=r60) (extendKnown (bound:=r61) (extendKnown (bound:=r62) (extendKnown (bound:=r63) (extendKnown (bound:=r64) (extendKnown (bound:=r65) (extendKnown (bound:=r66) (extendKnown (bound:=r67) (extendKnown (bound:=r68) (extendKnown (bound:=r69) (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) r69p) r68p) r67p) r66p) r65p) r64p) r63p) r62p) r61p) r60p) r59p) r10p) r58p) r57p) r56p) r55p) r54p) r53p) r44p) r43p) r42p) r41p) r40p) r39p) r20p) r0p) (by decide +kernel) (by decide +kernel) c5B0n2265

end PEqualNP.Outside.L_meta_8397

open PEqualNP.Outside.L_meta_8397 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_8397 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 6) || (x 5 && x 7)) t → 14 ≤ t := by
  intro t h
  let raw : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let target : BitVec 256 := 0xffffffffffeeffecffffffffffeaffe8ffffffffffeeeeecffeeeeecffeaeae8
  have lower : Lower (fullMask 256) (raw.map BitVec.toNat) target.toNat 14 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) c5Proof
  exact hcsLower (n := 8) raw target 14 _ (by decide +kernel) (by decide +kernel) lower t h
