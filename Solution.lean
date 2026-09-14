/-!
# Typed two-dimensional conversion evidence

This file proves the Palomar challenge extracted from Sections 2, 3, and 7 of
"A Theory of a Two-Dimensional Typed Lambda Calculus".  `Step` records labelled
one-step conversions, `Path` records finite sequences of steps, and `Step2` and
`Path2` record the declared two-dimensional identifications.  The principal
claim is that a structural parity is preserved by every cell.  Consequently,
the beta contraction of `(fun x => u x) a` and the eta contraction inside the
application context are distinct evidence with the same endpoints, and their
composite gives a loop that is not connected to the empty path.

The object types are universe-polymorphic but are kept in one universe at a
time.  The evidence families live one universe higher so that function-valued
premises remain inspectable data.
-/

namespace TDLC

universe u

/-- Labelled one-step conversions between terms. -/
inductive Step : {α : Type u} → α → α → Type (u + 1) where
  | beta {A B : Type u} (f : A → B) (a : A) :
      Step ((fun x => f x) a) (f a)
  | eta {A B : Type u} (f : A → B) :
      Step (fun x => f x) f
  | apCong {A B : Type u} (f : A → B) {x y : A} :
      Step x y → Step (f x) (f y)
  | lamCong {A B : Type u} {f g : A → B} :
      ((x : A) → Step (f x) (g x)) → Step f g
  | refl {A : Type u} (x : A) : Step x x
  | sym {A : Type u} {x y : A} : Step x y → Step y x
  | trans {A : Type u} {x y z : A} : Step x y → Step y z → Step x z

/-- Finite sequences of labelled steps. -/
inductive Path : {α : Type u} → α → α → Type (u + 1) where
  | nil {A : Type u} (x : A) : Path x x
  | seq {A : Type u} {x y z : A} : Step x y → Path y z → Path x z

namespace Path

/-- Concatenation, recursively exposing the first path. -/
def concat {A : Type u} {x y z : A} : Path x y → Path y z → Path x z
  | .nil _, q => q
  | .seq s p, q => .seq s (concat p q)

infixr:65 " ++ₚ " => concat

/-- Embed one step as a singleton path. -/
def lEmbed {A : Type u} {x y : A} (s : Step x y) : Path x y :=
  .seq s (.nil y)

/-- Reverse a path and explicitly symmetrise every step. -/
def inv {A : Type u} {x y : A} : Path x y → Path y x
  | .nil _ => .nil _
  | .seq s p => inv p ++ₚ lEmbed (.sym s)

/-- Functorial action of a host-language function on labelled paths. -/
def ap {A B : Type u} (f : A → B) {x y : A} : Path x y → Path (f x) (f y)
  | .nil _ => .nil _
  | .seq s p => .seq (.apCong f s) (ap f p)

/-- Compress a path into one structural step. -/
def toStep {A : Type u} {x y : A} : Path x y → Step x y
  | .nil _ => .refl _
  | .seq s p => .trans s (toStep p)

end Path

/-- Host-language eta expansion, named so its congruence remains visible. -/
def etaExpand {A B : Type u} (f : A → B) : A → B := fun x => f x

/-- Two-cells between parallel paths, with exactly the generators used by the paper. -/
inductive Step2 : {A : Type u} → {x y : A} → Path x y → Path x y → Type (u + 1) where
  | cReflStep {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.refl x) ++ₚ Path.lEmbed s)
        (Path.lEmbed s ++ₚ Path.lEmbed (.refl y))
  | betaStep {A B : Type u} (f : A → B) {a b : A} (s : Step a b) :
      Step2 (Path.ap (fun x => f x) (Path.lEmbed s) ++ₚ Path.lEmbed (.beta f b))
        (Path.lEmbed (.beta f a) ++ₚ Path.ap f (Path.lEmbed s))
  | etaStep {A B : Type u} {f g : A → B} (s : Step f g) :
      Step2 (Path.ap etaExpand (Path.lEmbed s) ++ₚ Path.lEmbed (.eta g))
        (Path.lEmbed (.eta f) ++ₚ Path.lEmbed s)
  | lamCongStep {A B : Type u} {f g : A → B}
      (h : (x : A) → Step (f x) (g x)) {a b : A} (s : Step a b) :
      Step2
        (Path.ap f (Path.lEmbed s) ++ₚ
          Path.lEmbed (.apCong (fun k : A → B => k b) (.lamCong h)))
        (Path.lEmbed (.apCong (fun k : A → B => k a) (.lamCong h)) ++ₚ
          Path.ap g (Path.lEmbed s))
  | refl2 {A : Type u} {x y : A} (p : Path x y) : Step2 p p
  | sym2 {A : Type u} {x y : A} {p q : Path x y} : Step2 p q → Step2 q p
  | trans2 {A : Type u} {x y : A} {p q r : Path x y} :
      Step2 p q → Step2 q r → Step2 p r
  | reflStep2 {A : Type u} (x : A) :
      Step2 (Path.lEmbed (.refl x)) (.nil x)
  | symStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.sym s)) (Path.inv (Path.lEmbed s))
  | transStep2 {A : Type u} {x y z : A} (s : Step x y) (t : Step y z) :
      Step2 (Path.lEmbed (.trans s t)) (Path.lEmbed s ++ₚ Path.lEmbed t)
  | leftInvStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.inv (Path.lEmbed s) ++ₚ Path.lEmbed s) (.nil y)
  | rightInvStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed s ++ₚ Path.inv (Path.lEmbed s)) (.nil x)
  | symSymStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.sym (.sym s))) (Path.lEmbed s)
  | apCongIdStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.ap (fun t => t) (Path.lEmbed s)) (Path.lEmbed s)
  | apCongStep2 {A B : Type u} (f : A → B) {x y : A} {p q : Path x y} :
      Step2 p q → Step2 (Path.ap f p) (Path.ap f q)
  | apCongComposeStep2 {A B C : Type u} (g : B → C) (f : A → B)
      {x y : A} (s : Step x y) :
      Step2 (Path.ap g (Path.ap f (Path.lEmbed s)))
        (Path.ap (fun z => g (f z)) (Path.lEmbed s))
  | cong2 {A : Type u} {x y z : A} (s : Step x y) {p q : Path y z} :
      Step2 p q → Step2 (.seq s p) (.seq s q)
  | whiskR2 {A : Type u} {w x y : A} {p q : Path w x} :
      Step2 p q → (r : Path x y) → Step2 (p ++ₚ r) (q ++ₚ r)

/-- Sequences of two-cells retain an explicit pasting presentation. -/
inductive Path2 {A : Type u} {x y : A} : (p q : Path x y) → Type (u + 1) where
  | nil2 (p : Path x y) : Path2 p p
  | seq2 {p q r : Path x y} : Step2 p q → Path2 q r → Path2 p r

namespace Step2

/-- Frame a two-cell on the left by an arbitrary path. -/
def whiskL {A : Type u} {w x y : A} :
    (r : Path w x) → {p q : Path x y} →
      Step2 p q → Step2 (r ++ₚ p) (r ++ₚ q)
  | .nil _, _, _, cell => cell
  | .seq s r, _, _, cell => .cong2 s (whiskL r cell)

/-- The empty path is a right identity, witnessed by a two-cell. -/
def rightId {A : Type u} {x y : A} :
    (p : Path x y) → Step2 (p ++ₚ .nil y) p
  | .nil _ => .refl2 _
  | .seq s p => .cong2 s (rightId p)

/-- Concatenation is associative up to a constructed two-cell. -/
def assoc {A : Type u} {w x y z : A} :
    (p : Path w x) → (q : Path x y) → (r : Path y z) →
      Step2 ((p ++ₚ q) ++ₚ r) (p ++ₚ (q ++ₚ r))
  | .nil _, _, r => .refl2 _
  | .seq s p, q, r => .cong2 s (assoc p q r)

/-- Horizontal composition, derived from the two whiskerings. -/
def horizontal {A : Type u} {x y z : A} {p₁ q₁ : Path x y}
    {p₂ q₂ : Path y z} (first : Step2 p₁ q₁) (second : Step2 p₂ q₂) :
    Step2 (p₁ ++ₚ p₂) (q₁ ++ₚ q₂) :=
  .trans2 (.whiskR2 first p₂) (whiskL q₁ second)

/-- Reflexivity commutes with every path. -/
def cRefl {A : Type u} {x y : A} :
    (p : Path x y) →
      Step2 (Path.lEmbed (.refl x) ++ₚ p) (p ++ₚ Path.lEmbed (.refl y))
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2 (.whiskR2 (.cReflStep s) p)
        (whiskL (Path.lEmbed s) (cRefl p))

/-- Compression of a path to a structural step is coherent with the path. -/
def pathToStepCoherence {A : Type u} {x y : A} :
    (p : Path x y) → Step2 (Path.lEmbed (Path.toStep p)) p
  | .nil x => .reflStep2 x
  | .seq s p =>
      .trans2 (.transStep2 s (Path.toStep p))
        (whiskL (Path.lEmbed s) (pathToStepCoherence p))

/-- The beta naturality square extends constructively from steps to paths. -/
def betaPath {A B : Type u} (f : A → B) {x y : A} :
    (p : Path x y) → Step2
      (Path.ap (fun a => f a) p ++ₚ Path.lEmbed (.beta f y))
      (Path.lEmbed (.beta f x) ++ₚ Path.ap f p)
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (whiskL (Path.lEmbed (.apCong (fun a => f a) s)) (betaPath f p))
        (.whiskR2 (.betaStep f s) (Path.ap f p))

/-- The eta naturality square extends constructively from steps to paths. -/
def etaPath {A B : Type u} {f g : A → B} (p : Path f g) :
    Step2
      (Path.ap etaExpand p ++ₚ Path.lEmbed (.eta g))
      (Path.lEmbed (.eta f) ++ₚ p) := by
  let coherence := pathToStepCoherence p
  exact .trans2
    (.whiskR2 (.sym2 (.apCongStep2 etaExpand coherence)) (Path.lEmbed (.eta g)))
    (.trans2 (.etaStep (Path.toStep p))
      (whiskL (Path.lEmbed (.eta f)) coherence))

/-- Lambda-congruence naturality extends constructively from steps to paths. -/
def lamCongPath {A B : Type u} {f g : A → B}
    (h : (x : A) → Step (f x) (g x)) {x y : A} :
    (p : Path x y) → Step2
      (Path.ap f p ++ₚ
        Path.lEmbed (.apCong (fun k : A → B => k y) (.lamCong h)))
      (Path.lEmbed (.apCong (fun k : A → B => k x) (.lamCong h)) ++ₚ
        Path.ap g p)
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (whiskL (Path.lEmbed (.apCong f s)) (lamCongPath h p))
        (.whiskR2 (.lamCongStep h s) (Path.ap g p))

/-- Congruence by the identity function is coherent on every path. -/
def apId {A : Type u} {x y : A} :
    (p : Path x y) → Step2 (Path.ap (fun t => t) p) p
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (.whiskR2 (.apCongIdStep2 s) (Path.ap (fun t => t) p))
        (whiskL (Path.lEmbed s) (apId p))

/-- Congruence respects composition of host-language functions on every path. -/
def apCompose {A B C : Type u} (g : B → C) (f : A → B)
    {x y : A} : (p : Path x y) →
    Step2 (Path.ap g (Path.ap f p)) (Path.ap (fun z => g (f z)) p)
  | .nil _ => .refl2 _
  | .seq s p =>
      .trans2
        (.whiskR2 (.apCongComposeStep2 g f s) (Path.ap g (Path.ap f p)))
        (whiskL (Path.lEmbed (.apCong (fun z => g (f z)) s)) (apCompose g f p))

/-- Congruence distributes over concatenation. -/
def apConcat {A B : Type u} (f : A → B) {x y z : A} :
    (p : Path x y) → (q : Path y z) →
      Step2 (Path.ap f (p ++ₚ q)) (Path.ap f p ++ₚ Path.ap f q)
  | .nil _, q => .refl2 _
  | .seq s p, q => .cong2 (.apCong f s) (apConcat f p q)

/-- Naturality is closed under pointwise symmetry, using only coherence and cancellation. -/
def reverseNaturality {A B : Type u} {f g : A → B}
    (h : (x : A) → Step (f x) (g x)) {x y : A} (p : Path x y)
    (cell : Step2
      (Path.ap f p ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g p)) :
    Step2
      (Path.ap g p ++ₚ Path.lEmbed (.sym (h y)))
      (Path.lEmbed (.sym (h x)) ++ₚ Path.ap f p) := by
  let hx := Path.lEmbed (h x)
  let hy := Path.lEmbed (h y)
  let ihx := Path.inv hx
  let ihy := Path.inv hy
  let fp := Path.ap f p
  let gp := Path.ap g p
  exact .trans2
    (.whiskR2 (.sym2 (.leftInvStep2 (h x))) (gp ++ₚ ihy))
    (.trans2 (assoc ihx hx (gp ++ₚ ihy))
      (.trans2 (whiskL ihx (.sym2 (assoc hx gp ihy)))
        (.trans2 (whiskL ihx (.whiskR2 (.sym2 cell) ihy))
          (.trans2 (whiskL ihx (assoc fp hy ihy))
            (.trans2 (whiskL ihx (whiskL fp (.rightInvStep2 (h y))))
              (whiskL ihx (rightId fp)))))))

/-- Naturality is closed under pointwise transitivity. -/
def transNaturality {A B : Type u} {f g k : A → B}
    (h : (x : A) → Step (f x) (g x))
    (d : (x : A) → Step (g x) (k x)) {x y : A} (p : Path x y)
    (first : Step2
      (Path.ap f p ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g p))
    (second : Step2
      (Path.ap g p ++ₚ Path.lEmbed (d y))
      (Path.lEmbed (d x) ++ₚ Path.ap k p)) :
    Step2
      (Path.ap f p ++ₚ Path.lEmbed (.trans (h y) (d y)))
      (Path.lEmbed (.trans (h x) (d x)) ++ₚ Path.ap k p) := by
  let fp := Path.ap f p
  let gp := Path.ap g p
  let kp := Path.ap k p
  let hx := Path.lEmbed (h x)
  let hy := Path.lEmbed (h y)
  let dx := Path.lEmbed (d x)
  let dy := Path.lEmbed (d y)
  exact .trans2
    (whiskL fp (.transStep2 (h y) (d y)))
    (.trans2 (.sym2 (assoc fp hy dy))
      (.trans2 (.whiskR2 first dy)
        (.trans2 (assoc hx gp dy)
          (.trans2 (whiskL hx second)
            (.trans2 (.sym2 (assoc hx dx kp))
              (.whiskR2 (.sym2 (.transStep2 (h x) (d x))) kp))))))

/-- Naturality is preserved by congruence with a host-language function. -/
def mapNaturality {A B C : Type u} (v : B → C)
    {f g : A → B} (h : (x : A) → Step (f x) (g x))
    {x y : A} (p : Path x y)
    (cell : Step2
      (Path.ap f p ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g p)) :
    Step2
      (Path.ap (fun z => v (f z)) p ++ₚ Path.lEmbed (.apCong v (h y)))
      (Path.lEmbed (.apCong v (h x)) ++ₚ Path.ap (fun z => v (g z)) p) := by
  let fp := Path.ap f p
  let gp := Path.ap g p
  let vfp := Path.ap v fp
  let vgp := Path.ap v gp
  exact .trans2
    (.whiskR2 (.sym2 (apCompose v f p)) (Path.lEmbed (.apCong v (h y))))
    (.trans2 (.sym2 (apConcat v fp (Path.lEmbed (h y))))
      (.trans2 (.apCongStep2 v cell)
        (.trans2 (apConcat v (Path.lEmbed (h x)) gp)
          (whiskL (Path.lEmbed (.apCong v (h x))) (apCompose v g p)))))

end Step2

/-- An inductive language of globally presented pointwise step homotopies. -/
inductive HomotopyStepI : {A B : Type u} → (A → B) → (A → B) → Type (u + 1) where
  | refl {A B : Type u} (f : A → B) : HomotopyStepI f f
  | beta {A B : Type u} (f : A → B) : HomotopyStepI (fun x => f x) f
  | eta {A B : Type u} :
      HomotopyStepI (@etaExpand A B) (fun f => f)
  | apCong {A B C : Type u} (v : B → C) {f g : A → B} :
      HomotopyStepI f g →
      HomotopyStepI (fun x => v (f x)) (fun x => v (g x))
  | sym {A B : Type u} {f g : A → B} :
      HomotopyStepI f g → HomotopyStepI g f
  | trans {A B : Type u} {f g k : A → B} :
      HomotopyStepI f g → HomotopyStepI g k → HomotopyStepI f k
  | lamCong {A B : Type u} {f g : A → B} :
      HomotopyStepI f g → HomotopyStepI f g

/-- A computed pointwise family paired with its naturality square for every path. -/
structure CertifiedStepEvaluation {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) : Type (u + 1) where
  family : (x : A) → Step (f x) (g x)
  naturality : {x y : A} → (p : Path x y) →
    Step2
      (Path.ap f p ++ₚ Path.lEmbed (family y))
      (Path.lEmbed (family x) ++ₚ Path.ap g p)

/-- Canonical evaluation of the presented homotopy language.

The definition performs structural recursion on the presentation.  Each branch
chooses the displayed pointwise step and constructs its naturality certificate
from the primitive two-cells and the derived path algebra above. -/
def evalHomotopyStepI {A B : Type u} {f g : A → B} :
    (e : HomotopyStepI f g) → CertifiedStepEvaluation e
  | .refl f =>
      {
        family := fun x => .refl (f x)
        naturality := fun p => .sym2 (Step2.cRefl (Path.ap f p))
      }
  | .beta f =>
      {
        family := fun x => .beta f x
        naturality := fun p => Step2.betaPath f p
      }
  | @HomotopyStepI.eta A B =>
      {
        family := fun f => .eta f
        naturality := fun p =>
          .trans2 (Step2.etaPath p)
            (Step2.whiskL (Path.lEmbed (.eta _)) (.sym2 (Step2.apId p)))
      }
  | .apCong v e =>
      {
        family := fun x => .apCong v ((evalHomotopyStepI e).family x)
        naturality := fun p => Step2.mapNaturality v (evalHomotopyStepI e).family p
          ((evalHomotopyStepI e).naturality p)
      }
  | .sym e =>
      {
        family := fun x => .sym ((evalHomotopyStepI e).family x)
        naturality := fun p => Step2.reverseNaturality (evalHomotopyStepI e).family p
          ((evalHomotopyStepI e).naturality p)
      }
  | .trans first second =>
      {
        family := fun x => .trans ((evalHomotopyStepI first).family x)
          ((evalHomotopyStepI second).family x)
        naturality := fun p =>
          Step2.transNaturality (evalHomotopyStepI first).family
            (evalHomotopyStepI second).family p
            ((evalHomotopyStepI first).naturality p)
            ((evalHomotopyStepI second).naturality p)
      }
  | .lamCong e =>
      {
        family := fun x =>
          .apCong (fun k => k x) (.lamCong (evalHomotopyStepI e).family)
        naturality := fun p => Step2.lamCongPath (evalHomotopyStepI e).family p
      }

/-- The canonical evaluator exposes its computed family, not merely a certificate field. -/
theorem evalHomotopyStepI_refl {A B : Type u} (f : A → B) (x : A) :
    (evalHomotopyStepI (.refl f)).family x = Step.refl (f x) := rfl

theorem evalHomotopyStepI_beta {A B : Type u} (f : A → B) (x : A) :
    (evalHomotopyStepI (.beta f)).family x = Step.beta f x := rfl

theorem evalHomotopyStepI_eta {A B : Type u} (f : A → B) :
    (evalHomotopyStepI (@HomotopyStepI.eta A B)).family f = Step.eta f := rfl

theorem evalHomotopyStepI_apCong {A B C : Type u} (v : B → C)
    {f g : A → B} (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.apCong v e)).family x =
      Step.apCong v ((evalHomotopyStepI e).family x) := rfl

theorem evalHomotopyStepI_sym {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.sym e)).family x =
      Step.sym ((evalHomotopyStepI e).family x) := rfl

theorem evalHomotopyStepI_trans {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (d : HomotopyStepI g k) (x : A) :
    (evalHomotopyStepI (.trans e d)).family x =
      Step.trans ((evalHomotopyStepI e).family x)
        ((evalHomotopyStepI d).family x) := rfl

theorem evalHomotopyStepI_lamCong {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.lamCong e)).family x =
      Step.apCong (fun k : A → B => k x)
        (Step.lamCong (evalHomotopyStepI e).family) := rfl

/-- Every presented homotopy receives a constructed naturality square. -/
def certifiedStepNaturality {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Step2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) :=
  (evalHomotopyStepI e).naturality p

/-- A global finite presentation made from certified step presentations. -/
inductive HomotopyPathI : {A B : Type u} → (A → B) → (A → B) → Type (u + 1) where
  | nil {A B : Type u} (f : A → B) : HomotopyPathI f f
  | seq {A B : Type u} {f g k : A → B} :
      HomotopyStepI f g → HomotopyPathI g k → HomotopyPathI f k

/-- Pointwise evaluation of a global presented homotopy path. -/
def evalHomotopyPathI {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → (x : A) → Path (f x) (g x)
  | .nil f, x => .nil (f x)
  | .seq e hp, x =>
      .seq ((evalHomotopyStepI e).family x) (evalHomotopyPathI hp x)

theorem evalHomotopyPathI_nil {A B : Type u} (f : A → B) (x : A) :
    evalHomotopyPathI (.nil f) x = Path.nil (f x) := rfl

theorem evalHomotopyPathI_seq {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k) (x : A) :
    evalHomotopyPathI (.seq e hp) x =
      Path.seq ((evalHomotopyStepI e).family x) (evalHomotopyPathI hp x) := rfl

/-- Direct naturality for a global presented homotopy path. -/
def evaluatedPathNaturalityCell {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → (p : Path x y) →
    Step2
      (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p)
  | .nil f, _, _, p => Step2.rightId (Path.ap f p)
  | @HomotopyPathI.seq _ _ f g k e hp, x, y, p =>
      let ev := evalHomotopyStepI e
      let fp := Path.ap f p
      let gp := Path.ap g p
      let kp := Path.ap k p
      let hx := Path.lEmbed (ev.family x)
      let hy := Path.lEmbed (ev.family y)
      let rx := evalHomotopyPathI hp x
      let ry := evalHomotopyPathI hp y
      .trans2 (.sym2 (Step2.assoc fp hy ry))
        (.trans2 (.whiskR2 (ev.naturality p) ry)
          (.trans2 (Step2.assoc hx gp ry)
            (.trans2 (Step2.whiskL hx (evaluatedPathNaturalityCell hp p))
              (.sym2 (Step2.assoc hx rx kp)))))

namespace Path2

/-- Embed one two-cell as a one-entry two-path. -/
def singleton {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) : Path2 p q := .seq2 cell (.nil2 q)

/-- Collapse a finite presentation of two-cells to one composite cell. -/
def toCell {A : Type u} {x y : A} {p q : Path x y} :
    (cells : Path2 p q) → Step2 p q
  | .nil2 p => .refl2 p
  | .seq2 cell cells => .trans2 cell (toCell cells)

/-- Left-whisker every entry of a two-path. -/
def whiskL {A : Type u} {w x y : A} (r : Path w x) {p q : Path x y} :
    (cells : Path2 p q) → Path2 (r ++ₚ p) (r ++ₚ q)
  | .nil2 p => .nil2 _
  | .seq2 cell cells => .seq2 (Step2.whiskL r cell) (whiskL r cells)

/-- Right-whisker every entry of a two-path. -/
def whiskR {A : Type u} {x y z : A} {p q : Path x y} :
    (cells : Path2 p q) → (r : Path y z) → Path2 (p ++ₚ r) (q ++ₚ r)
  | .nil2 p, r => .nil2 _
  | .seq2 cell cells, r => .seq2 (.whiskR2 cell r) (whiskR cells r)

end Path2

/-- Direct naturality retained as an explicit finite two-path. -/
def certifiedPathNaturality {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p) :=
  Path2.singleton (evaluatedPathNaturalityCell hp p)

/-- Conjugation transport along one canonically evaluated step presentation. -/
def transportAlongPresented {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) (q : Path (f x) (f y)) :
    Path (g x) (g y) :=
  let ev := evalHomotopyStepI e
  Path.inv (Path.lEmbed (ev.family x)) ++ₚ
    (q ++ₚ Path.lEmbed (ev.family y))

/-- Conjugation transport respects every finite two-path. -/
def transportAlongPresentedRespects {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} {q r : Path (f x) (f y)}
    (cells : Path2 q r) :
    Path2 (transportAlongPresented e x y q) (transportAlongPresented e x y r) :=
  let ev := evalHomotopyStepI e
  Path2.whiskL (Path.inv (Path.lEmbed (ev.family x)))
    (Path2.whiskR cells (Path.lEmbed (ev.family y)))

/-- Transport sends the congruence path of the source function to that of the target. -/
def certifiedTransportCell {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Step2 (transportAlongPresented e x y (Path.ap f p)) (Path.ap g p) := by
  let ev := evalHomotopyStepI e
  let hx := Path.lEmbed (ev.family x)
  let hy := Path.lEmbed (ev.family y)
  let ihx := Path.inv hx
  let fp := Path.ap f p
  let gp := Path.ap g p
  exact .trans2 (Step2.whiskL ihx (ev.naturality p))
    (.trans2 (.sym2 (Step2.assoc ihx hx gp))
      (.whiskR2 (.leftInvStep2 (ev.family x)) gp))

/-- The transport comparison as an explicit two-path. -/
def certifiedTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2 (transportAlongPresented e x y (Path.ap f p)) (Path.ap g p) :=
  Path2.singleton (certifiedTransportCell e p)

/-- A comparison out of conjugation transport recovers the corresponding square. -/
def recoverNaturalityFromTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} {q : Path (f x) (f y)}
    {r : Path (g x) (g y)}
    (cells : Path2 (transportAlongPresented e x y q) r) :
    Path2
      (q ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ r) := by
  let ev := evalHomotopyStepI e
  let hx := Path.lEmbed (ev.family x)
  let ihx := Path.inv hx
  let source := q ++ₚ Path.lEmbed (ev.family y)
  exact Path2.singleton
    (.trans2 (.whiskR2 (.sym2 (.rightInvStep2 (ev.family x))) source)
      (.trans2 (Step2.assoc hx ihx source)
        (Step2.whiskL hx (Path2.toCell cells))))

/-- Naturality reconstructed through transport, whose comparison uses step naturality. -/
def certifiedNaturalityViaTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) :=
  recoverNaturalityFromTransport e (certifiedTransport e p)

/-- Recursive transport along an arbitrary finite global presentation. -/
def transportAlongPathI {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → (x y : A) →
    Path (f x) (f y) → Path (g x) (g y)
  | .nil _, _, _, q => q
  | .seq e hp, x, y, q =>
      transportAlongPathI hp x y (transportAlongPresented e x y q)

theorem transportAlongPathI_nil {A B : Type u} (f : A → B)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.nil f) x y q = q := rfl

theorem transportAlongPathI_seq {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.seq e hp) x y q =
      transportAlongPathI hp x y (transportAlongPresented e x y q) := rfl

/-- Recursive transport preserves finite two-path witnesses. -/
def transportAlongPathIRespects {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → {q r : Path (f x) (f y)} →
    Path2 q r →
    Path2 (transportAlongPathI hp x y q) (transportAlongPathI hp x y r)
  | .nil _, _, _, _, _, cells => cells
  | .seq e hp, _, _, _, _, cells =>
      transportAlongPathIRespects hp (transportAlongPresentedRespects e cells)

/-- The comparison is derived from step naturality, recursively over the presentation. -/
def certifiedPathTransport {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → (p : Path x y) →
    Path2 (transportAlongPathI hp x y (Path.ap f p)) (Path.ap g p)
  | .nil _, _, _, p => .nil2 _
  | .seq e hp, _, _, p =>
      Path2.singleton (.trans2
        (Path2.toCell (transportAlongPathIRespects hp (certifiedTransport e p)))
        (Path2.toCell (certifiedPathTransport hp p)))

/-- Recover a square from any comparison out of recursive transport. -/
def recoverNaturalityFromPathTransport {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} →
    {q : Path (f x) (f y)} → {r : Path (g x) (g y)} →
    Path2 (transportAlongPathI hp x y q) r →
    Path2 (q ++ₚ evalHomotopyPathI hp y) (evalHomotopyPathI hp x ++ₚ r)
  | .nil _, _, _, q, _, cells =>
      Path2.singleton (.trans2 (Step2.rightId q) (Path2.toCell cells))
  | .seq e hp, x, y, q, r, cells =>
      let hx := Path.lEmbed ((evalHomotopyStepI e).family x)
      let hy := Path.lEmbed ((evalHomotopyStepI e).family y)
      let rx := evalHomotopyPathI hp x
      let ry := evalHomotopyPathI hp y
      let tq := transportAlongPresented e x y q
      let first := Path2.toCell (recoverNaturalityFromTransport e (.nil2 tq))
      let rest := Path2.toCell (recoverNaturalityFromPathTransport hp cells)
      Path2.singleton (.trans2 (.sym2 (Step2.assoc q hy ry))
        (.trans2 (.whiskR2 first ry)
          (.trans2 (Step2.assoc hx tq ry)
            (.trans2 (Step2.whiskL hx rest) (.sym2 (Step2.assoc hx rx r))))))

/-- A transport-based reconstruction, not an independent proof of naturality. -/
def certifiedPathNaturalityViaTransport {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) {x y : A} (p : Path x y) :
    Path2 (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p) :=
  recoverNaturalityFromPathTransport hp (certifiedPathTransport hp p)

namespace Step

/-- The outer constructor of a step, used to expose the evaluator's uniform grammar. -/
def headTag {A : Type u} {x y : A} : Step x y → Nat
  | @TDLC.Step.beta _ _ f a => 0
  | @TDLC.Step.eta _ _ f => 1
  | @TDLC.Step.apCong _ _ f _ _ s => 2
  | @TDLC.Step.lamCong _ _ f g h => 3
  | @TDLC.Step.refl _ x => 4
  | @TDLC.Step.sym _ _ _ s => 5
  | @TDLC.Step.trans _ _ _ _ s t => 6

end Step

/-- A global presentation evaluates to the same outer step form at every point. -/
theorem evaluatedHeadTagConstant {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) :
    Step.headTag ((evalHomotopyStepI e).family x) =
      Step.headTag ((evalHomotopyStepI e).family y) := by
  induction e <;> rfl

/-- A semantic pointwise family whose outer evidence form genuinely varies by point. -/
def mixedUnitFamily : (b : Bool) → Step Unit.unit Unit.unit
  | false => .beta (fun x : Unit => x) Unit.unit
  | true => .refl Unit.unit

/-- Presented homotopies are a proper subclass of arbitrary semantic step families.

This is the formal obstruction needed to keep the certified theorem honest: the
canonical evaluator cannot silently stand for every pointwise family.  It does not,
by itself, assert that the displayed family lacks every possible naturality cell. -/
theorem semanticFamilyNotPresented :
    ¬ ∃ e : HomotopyStepI (fun _ : Bool => Unit.unit) (fun _ : Bool => Unit.unit),
      ∀ b, (evalHomotopyStepI e).family b = mixedUnitFamily b := by
  rintro ⟨e, h⟩
  have uniform := evaluatedHeadTagConstant e false true
  rw [h false, h true] at uniform
  have impossible : (0 : Nat) = 4 := by
    exact uniform
  exact Nat.noConfusion impossible

/-- Boolean exclusive-or, used as addition in the two-element grading. -/
def bxor : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

namespace Step

/-- Structural parity: beta contributes one; eta and lambda congruence contribute zero. -/
def parity {A : Type u} {x y : A} : Step x y → Bool
  | @TDLC.Step.beta _ _ f a => true
  | @TDLC.Step.eta _ _ f => false
  | @TDLC.Step.apCong _ _ f _ _ s => parity s
  | @TDLC.Step.lamCong _ _ f g h => false
  | @TDLC.Step.refl _ x => false
  | @TDLC.Step.sym _ _ _ s => parity s
  | @TDLC.Step.trans _ _ _ _ s t => bxor (parity s) (parity t)

end Step

namespace Path

/-- XOR-sum of structural parities along a path. -/
def parity {A : Type u} {x y : A} : Path x y → Bool
  | .nil _ => false
  | .seq s p => bxor (Step.parity s) (parity p)

end Path

@[simp] theorem bxor_false_left (b : Bool) : bxor false b = b := rfl

@[simp] theorem bxor_false_right (b : Bool) : bxor b false = b := by
  cases b <;> rfl

@[simp] theorem bxor_self (b : Bool) : bxor b b = false := by
  cases b <;> rfl

theorem bxor_comm (a b : Bool) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl

theorem bxor_assoc (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem Path.parity_lEmbed {A : Type u} {x y : A} (s : Step x y) :
    Path.parity (Path.lEmbed s) = Step.parity s := by
  change bxor (Step.parity s) false = Step.parity s
  exact bxor_false_right _

@[simp] theorem Path.parity_concat {A : Type u} {x y z : A}
    (p : Path x y) (q : Path y z) :
    Path.parity (p ++ₚ q) = bxor (Path.parity p) (Path.parity q) := by
  induction p with
  | nil => rfl
  | seq s p ih =>
      change
        bxor (Step.parity s) (Path.parity (p ++ₚ q)) =
          bxor (bxor (Step.parity s) (Path.parity p)) (Path.parity q)
      rw [ih]
      exact (bxor_assoc _ _ _).symm

@[simp] theorem Path.parity_inv {A : Type u} {x y : A} (p : Path x y) :
    Path.parity (Path.inv p) = Path.parity p := by
  induction p with
  | nil => rfl
  | seq s p ih =>
      rw [Path.inv, Path.parity_concat, ih, Path.parity_lEmbed]
      exact bxor_comm _ _

@[simp] theorem Path.parity_ap {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) : Path.parity (Path.ap f p) = Path.parity p := by
  induction p with
  | nil => rfl
  | seq s p ih =>
      change
        bxor (Step.parity s) (Path.parity (Path.ap f p)) =
          bxor (Step.parity s) (Path.parity p)
      rw [ih]

/-- Every declared generating or composite two-cell preserves structural parity. -/
theorem step2PreservesParity {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) : Path.parity p = Path.parity q := by
  induction cell with
  | cReflStep s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_lEmbed]
      change bxor false (Step.parity s) = bxor (Step.parity s) false
      exact bxor_comm _ _
  | betaStep f s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_ap]
      repeat rw [Path.parity_lEmbed]
      change bxor (Step.parity s) true = bxor true (Step.parity s)
      exact bxor_comm _ _
  | etaStep s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_ap]
      repeat rw [Path.parity_lEmbed]
      change bxor (Step.parity s) false = bxor false (Step.parity s)
      exact bxor_comm _ _
  | lamCongStep h s =>
      repeat rw [Path.parity_concat]
      repeat rw [Path.parity_ap]
      repeat rw [Path.parity_lEmbed]
      change bxor (Step.parity s) false = bxor false (Step.parity s)
      exact bxor_comm _ _
  | refl2 p => rfl
  | sym2 cell ih => exact ih.symm
  | trans2 first second ihFirst ihSecond => exact ihFirst.trans ihSecond
  | reflStep2 x =>
      rw [Path.parity_lEmbed]
      rfl
  | symStep2 s =>
      rw [Path.parity_lEmbed, Path.parity_inv, Path.parity_lEmbed]
      rfl
  | transStep2 s t =>
      rw [Path.parity_lEmbed, Path.parity_concat,
        Path.parity_lEmbed, Path.parity_lEmbed]
      rfl
  | leftInvStep2 s =>
      rw [Path.parity_concat, Path.parity_inv, Path.parity_lEmbed]
      change bxor (Step.parity s) (Step.parity s) = false
      exact bxor_self _
  | rightInvStep2 s =>
      rw [Path.parity_concat, Path.parity_inv, Path.parity_lEmbed]
      change bxor (Step.parity s) (Step.parity s) = false
      exact bxor_self _
  | symSymStep2 s =>
      rw [Path.parity_lEmbed, Path.parity_lEmbed]
      rfl
  | apCongIdStep2 s =>
      rw [Path.parity_ap]
  | apCongStep2 f cell ih =>
      rw [Path.parity_ap, Path.parity_ap]
      exact ih
  | apCongComposeStep2 g f s =>
      rw [Path.parity_ap, Path.parity_ap, Path.parity_ap]
  | cong2 s cell ih =>
      change
        bxor (Step.parity s) (Path.parity _) =
          bxor (Step.parity s) (Path.parity _)
      exact congrArg (bxor (Step.parity s)) ih
  | whiskR2 cell r ih =>
      rw [Path.parity_concat, Path.parity_concat]
      exact congrArg (fun b => bxor b (Path.parity r)) ih

/-- Every finite sequence of two-cells preserves structural parity. -/
theorem path2PreservesParity {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) : Path.parity p = Path.parity q := by
  induction cells with
  | nil2 p => rfl
  | seq2 cell cells ih => exact (step2PreservesParity cell).trans ih

/-- The beta-labelled and eta-labelled routes with the same endpoints cannot be joined. -/
theorem betaEtaSeparated {A B : Type u} (f : A → B) (a : A) :
    Step2
      (Path.lEmbed (Step.beta f a))
      (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))) → False := by
  intro cell
  have h := step2PreservesParity cell
  change true = false at h
  exact Bool.noConfusion h

/-- The beta/eta loop is not connected by any two-path to the empty path. -/
theorem betaEtaLoopNontrivial {A B : Type u} (f : A → B) (a : A) :
    Path2
      (Path.lEmbed (Step.beta f a) ++ₚ
        Path.inv (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))))
      (.nil (f a)) → False := by
  intro cells
  have h := path2PreservesParity cells
  change true = false at h
  exact Bool.noConfusion h

end TDLC
