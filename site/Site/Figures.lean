/-
Figure library for the jordan_pick Verso site.

All figures are `Illuminate.Diagram Illuminate.SVG` terms, rendered to inline
SVG at site build time by the Verso `diagram` code block. Conventions:

* Figure code works in *mathematical* coordinates (y up); the `Fig.P`
  constructor flips to SVG screen coordinates (y down) and applies the
  figure's scale.
* The lattice-point and ray-crossing data in the Pick figures is *computed*
  (point-in-polygon parity, edge lattice counts), not hard-coded, so the
  figures agree with the theorem by construction.
* Palette matches the site theme (`--jp-accent` blue), with red for
  "special/witness" objects and green for constructed paths.
-/
import Illuminate

open Illuminate

namespace Site.Figures

abbrev Fig := Diagram SVG

/-! ## Palette -/

def accent : Color := Color.rgb 9 105 218
def accentFill : Fill := .solid { color := Color.rgba 9 105 218 0.13 }
def accentFillStrong : Fill := .solid { color := Color.rgba 9 105 218 0.28 }
def crimson : Color := Color.rgb 207 34 46
def crimsonFill : Fill := .solid { color := Color.rgba 207 34 46 0.16 }
def leaf : Color := Color.rgb 26 127 55
def leafFill : Fill := .solid { color := Color.rgba 26 127 55 0.15 }
def ink : Color := Color.rgb 27 31 36
def gray : Color := Color.rgb 110 119 129
def grayFaint : Color := Color.rgba 110 119 129 0.45

def noFill : Fill := .none

/-! ## Geometry helpers (mathematical coordinates, y up) -/

/-- Diagram point from math coordinates at scale `u` (Illuminate is y-up). -/
def P (u x y : Float) : Vec2 := ⟨u * x, u * y⟩

/-- Closed polygon through math-coordinate points. -/
def polyClosed (u : Float) (pts : List (Float × Float))
    (fill : Fill := accentFill)
    (stroke : Stroke := { color := accent, width := 1.6 }) : Fig :=
  match pts with
  | [] => Diagram.emptyDiagram
  | (x, y) :: rest =>
    let pd := rest.foldl (fun pd (a, b) => pd.lineTo (P u a b))
      (PathData.moveTo (P u x y) .empty)
    Diagram.fromPath pd.close fill stroke

/-- Open polyline through math-coordinate points. -/
def polyOpen (u : Float) (pts : List (Float × Float))
    (stroke : Stroke := { color := ink, width := 1.6 }) : Fig :=
  match pts with
  | [] => Diagram.emptyDiagram
  | (x, y) :: rest =>
    let pd := rest.foldl (fun pd (a, b) => pd.lineTo (P u a b))
      (PathData.moveTo (P u x y) .empty)
    Diagram.fromStroke pd stroke

/-- Straight segment between math points. -/
def seg (u : Float) (a b : Float × Float)
    (stroke : Stroke := { color := ink, width := 1.4 }) : Fig :=
  Diagram.line (P u a.1 a.2) (P u b.1 b.2) stroke

/-- Filled dot at a math point. -/
def dot (u : Float) (p : Float × Float) (c : Color := ink) (r : Float := 3.2) : Fig :=
  Diagram.translate (u * p.1) (u * p.2)
    (Diagram.circle r (fill := .solid { color := c }) (stroke := { color := c, width := 0 }))

/-- Open (hollow) dot at a math point. -/
def odot (u : Float) (p : Float × Float) (c : Color := accent) (r : Float := 3.2) : Fig :=
  Diagram.translate (u * p.1) (u * p.2)
    (Diagram.circle r (fill := .solid { color := Color.white })
      (stroke := { color := c, width := 1.5 }))

/-- Text label at a math point. -/
def lbl (u : Float) (p : Float × Float) (s : String)
    (c : Color := ink) (size : Float := 13) (italic : Bool := true) : Fig :=
  Diagram.translate (u * p.1) (u * p.2)
    (Diagram.text s { fontFamily := "text", fontSize := size, italic := italic, color := c })

/-- Overlay a list of figures; later entries are drawn on top. -/
def ov (ds : List Fig) : Fig :=
  ds.foldl (fun acc d => Diagram.atop d acc) Diagram.emptyDiagram

/-- Sector at math point `v` covering math angles `[θ₁, θ₂]` (counterclockwise). -/
def sector (u : Float) (v : Float × Float) (θ₁ θ₂ r : Float)
    (fill : Fill) (stroke : Stroke := { color := gray, width := 0.8 }) : Fig :=
  Diagram.translate (u * v.1) (u * v.2)
    (Diagram.wedge θ₁ θ₂ (u * r) fill stroke)

def dashed (c : Color := gray) (w : Float := 1.2) : Stroke :=
  { color := c, width := w, dash := .dashed }

/-! ## Computed lattice data -/

/-- Edges of a polygon given by vertices (cyclically). -/
def edges (vs : List (Float × Float)) : List ((Float × Float) × (Float × Float)) :=
  vs.zip (vs.drop 1 ++ vs.take 1)

/-- Ray-casting parity: is `q` strictly inside the polygon (generic `q`)? -/
def insidePoly (vs : List (Float × Float)) (q : Float × Float) : Bool :=
  let cnt := (edges vs).foldl (fun c ((ax, ay), (bx, By)) =>
    if (ay > q.2) != (By > q.2) then
      let xInt := ax + (q.2 - ay) / (By - ay) * (bx - ax)
      if xInt > q.1 then c + 1 else c
    else c) 0
  cnt % 2 == 1

/-- Is `q` on the closed segment `[a, b]`? (exact for small integer data) -/
def onSeg (a b q : Float × Float) : Bool :=
  let cross := (b.1 - a.1) * (q.2 - a.2) - (b.2 - a.2) * (q.1 - a.1)
  let dotp := (q.1 - a.1) * (b.1 - a.1) + (q.2 - a.2) * (b.2 - a.2)
  let len2 := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2
  cross == 0 && 0 <= dotp && dotp <= len2

/-- Is `q` on the polygon boundary? -/
def onBoundary (vs : List (Float × Float)) (q : Float × Float) : Bool :=
  (edges vs).any fun (a, b) => onSeg a b q

/-- Integer grid points in `[0, w] × [0, h]`. -/
def grid (w h : Nat) : List (Float × Float) :=
  (List.range (w + 1)).flatMap fun i =>
    (List.range (h + 1)).map fun j => (Float.ofNat i, Float.ofNat j)

/-- Crossings of the rightward horizontal ray from `q` with the polygon:
`(crossing point, +1 for an up-crossing, −1 for down)`. -/
def rayCrossings (vs : List (Float × Float)) (q : Float × Float) :
    List ((Float × Float) × Int) :=
  (edges vs).filterMap fun ((ax, ay), (bx, By)) =>
    if (ay > q.2) != (By > q.2) then
      let xInt := ax + (q.2 - ay) / (By - ay) * (bx - ax)
      if xInt > q.1 then some ((xInt, q.2), if By > ay then 1 else -1) else none
    else none

/-! ## The running example polygon (Pick chapter)

Vertices `(0,0), (3,0), (4,2), (2,1), (1,3), (0,2)`: a simple non-convex
lattice hexagon with `2·area = 13` (shoelace), `B = 9`, `I = 3`, so
`area = 6.5 = 3 + 9/2 − 1`. -/

def pickPoly : List (Float × Float) := [(0, 0), (3, 0), (4, 2), (2, 1), (1, 3), (0, 2)]

/-- Interior lattice points of the running example (computed). -/
def pickInterior : List (Float × Float) :=
  (grid 4 3).filter fun p => !onBoundary pickPoly p && insidePoly pickPoly p

/-- Boundary lattice points of the running example (computed). -/
def pickBoundaryPts : List (Float × Float) :=
  (grid 4 3).filter (onBoundary pickPoly)

/-! ## Figure 1 — Pick's theorem statement -/

def pickStatement : Fig :=
  let u := 46.0
  ov <|
    -- faint lattice
    ((grid 4 3).map fun p => dot u p grayFaint 1.5) ++
    -- the polygon
    [polyClosed u pickPoly] ++
    -- boundary lattice points (open) and interior points (filled)
    (pickBoundaryPts.map fun p => odot u p accent 3.4) ++
    (pickInterior.map fun p => dot u p crimson 3.6) ++
    [lbl u (4.55, 0.4) "B = 9" accent 14,
     lbl u (4.55, 0.05) "(open)" gray 11 (italic := false),
     lbl u (1.6, 1.62) "I = 3" crimson 14,
     lbl u (2.0, -0.55) "area = I + B/2 − 1 = 6½" ink 14]

/-! ## Figure 2 — winding number as signed ray crossings -/

def windingFigure : Fig :=
  let u := 46.0
  let qIn : Float × Float := (0.55, 0.8)    -- winding 1
  let qOut : Float × Float := (0.4, 2.6)    -- winding 0 (ray crosses twice, cancelling)
  let far := 5.4
  let mark (c : (Float × Float) × Int) : List Fig :=
    [dot u c.1 (if c.2 == 1 then leaf else crimson) 3.4,
     lbl u (c.1.1, c.1.2 + 0.28) (if c.2 == 1 then "+1" else "−1")
       (if c.2 == 1 then leaf else crimson) 12 (italic := false)]
  ov <|
    [polyClosed u pickPoly] ++
    -- the two rays
    [seg u qIn (far, qIn.2) (dashed ink), seg u qOut (far, qOut.2) (dashed ink),
     dot u qIn ink 3.6, dot u qOut ink 3.6,
     lbl u (qIn.1 - 0.42, qIn.2) "w = 1" ink 13,
     lbl u (qOut.1 - 0.45, qOut.2) "w = 0" ink 13] ++
    ((rayCrossings pickPoly qIn).flatMap mark) ++
    ((rayCrossings pickPoly qOut).flatMap mark)

/-! ## Figure 3 — per-edge trapezoids (Green / shoelace) -/

def trapezoidFigure : Fig :=
  let u := 46.0
  let a : Float × Float := (0.5, 1.2)
  let b : Float × Float := (2.2, 2.6)
  let c : Float × Float := (3.8, 1.6)
  ov
    [ -- the x-axis
      seg u (-0.2, 0) (4.6, 0) { color := gray, width := 1.2 },
      -- trapezoid under edge b→c (traversed left→right: positive)
      polyClosed u [(b.1, 0), b, c, (c.1, 0)] accentFill { color := accent, width := 0 },
      -- trapezoid under edge c→a (traversed right→left: negative)
      polyClosed u [(a.1, 0), a, c, (c.1, 0)] crimsonFill { color := crimson, width := 0 },
      polyClosed u [a, b, c] noFill { color := ink, width := 1.8 },
      dot u a ink, dot u b ink, dot u c ink,
      lbl u (3.0, 0.75) "+" accent 20 (italic := false),
      lbl u (2.1, 0.4) "−" crimson 20 (italic := false),
      lbl u (2.2, -0.42) "area = Σ signed trapezoids = shoelace/2" ink 13
    ]

/-! ## Figure 4 — the lattice-point angle weight (count side) -/

def weightFigure : Fig :=
  let u := 46.0
  -- three panels: interior point (weight 1), edge point (1/2), vertex (θ/2π)
  let panel (cx : Float) (body : List Fig) (caption : String) : List Fig :=
    body ++ [lbl u (cx, -1.05) caption ink 13 (italic := false)]
  ov <|
    panel 0
      [sector u (0, 0) 0 6.283 0.62 accentFillStrong { color := accent, width := 0 },
       dot u (0, 0) ink 3.4] "weight 1" ++
    panel 3.0
      [seg u (1.9, 0) (4.1, 0) { color := ink, width := 1.8 },
       sector u (3.0, 0) 0 3.1415 0.62 accentFillStrong { color := accent, width := 0 },
       dot u (3.0, 0) ink 3.4] "weight ½" ++
    panel 6.0
      [seg u (6.0, 0) (7.1, 0.55) { color := ink, width := 1.8 },
       seg u (6.0, 0) (7.1, -0.4) { color := ink, width := 1.8 },
       sector u (6.0, 0) (-0.35) 0.46 0.62 accentFillStrong { color := accent, width := 0 },
       dot u (6.0, 0) ink 3.4,
       lbl u (6.95, 0.1) "θ" accent 13] "weight θ/2π"

/-! ## Figure 5 — ear clipping -/

def earClipFigure : Fig :=
  let u := 46.0
  ov
    [ polyClosed u pickPoly,
      -- the ear at vertex (1,3): triangle (2,1), (1,3), (0,2)
      polyClosed u [(2, 1), (1, 3), (0, 2)] crimsonFill { color := crimson, width := 0 },
      seg u (2, 1) (0, 2) (dashed crimson 1.6),
      dot u (1, 3) crimson 4.0,
      lbl u (1.35, 2.35) "ear" crimson 13,
      lbl u (2.0, -0.5) "clip the ear, recurse on the rest" ink 13
    ]

/-! ## Figure 6 — the tube cover: left/right regions and corner caps -/

def tubeFigure : Fig :=
  let u := 40.0
  -- vertex at the origin; incoming edge from A, outgoing to B
  let A : Float × Float := (-4.4, -1.0)
  let B : Float × Float := (3.4, 2.3)
  -- unit direction and left normal of each edge (computed by hand for clarity)
  -- edge1 dir d1 = v − A normalized; θA = angle of (A − v) [ray back along edge 1]
  let θA := Float.atan2 (-1.0 - 0) (-4.4 - 0) + 6.2832  -- ≈ 180°+…, normalized positive
  let θB := Float.atan2 2.3 3.4
  let ribbon (p q : Float × Float) (nx ny : Float) (fill : Fill) : Fig :=
    polyClosed u [p, q, (q.1 + nx, q.2 + ny), (p.1 + nx, p.2 + ny)] fill
      { color := gray, width := 0 }
  -- margins near the vertex so the ribbons stop where the caps take over
  let m1 : Float × Float := (-0.85, -0.19)   -- point on edge 1, short of v
  let m2 : Float × Float := (0.68, 0.46)     -- point on edge 2, short of v
  ov
    [ -- left (blue) and right (red) ribbons along both edges
      ribbon A m1 (0.21) (0.94) accentFill,
      ribbon A m1 (-0.21) (-0.94) crimsonFill,
      ribbon m2 B (-0.56) (0.83) accentFill,
      ribbon m2 B (0.56) (-0.83) crimsonFill,
      -- corner caps at the vertex: capB spans the left side, capA the right
      sector u (0, 0) θB θA 1.0 accentFillStrong,
      sector u (0, 0) (θA - 6.2832) θB 1.0 crimsonFill,
      -- the edges themselves
      seg u A (0, 0) { color := ink, width := 2.0 },
      seg u (0, 0) B { color := ink, width := 2.0 },
      dot u (0, 0) ink 4.0,
      dot u A ink 3.2, dot u B ink 3.2,
      -- the witness point q = v + ρ·dir(θ) just inside capB, just left of edge 2
      dot u (0.62 * Float.cos (θB + 0.35), 0.62 * Float.sin (θB + 0.35)) crimson 3.8,
      lbl u (0.62 * Float.cos (θB + 0.35) - 0.05, 0.62 * Float.sin (θB + 0.35) + 0.3)
        "q = v + ρ·dir θ" crimson 12,
      lbl u (-2.4, 0.85) "left region" accent 13,
      lbl u (-2.4, -1.35) "right region" crimson 13,
      lbl u (-0.75, 1.2) "cap B" accent 13,
      lbl u (0.9, -0.85) "cap A" crimson 13,
      lbl u (0.15, -0.32) "v" ink 13
    ]

/-! ## Figure 7 — crossing alternation along the ray -/

def alternationFigure : Fig :=
  let u := 46.0
  -- a boundary loop snaking across a horizontal ray
  let wave : List (Float × Float) :=
    [(0.0, -0.8), (0.7, 0.7), (1.4, 0.9), (2.0, -0.6), (2.6, -0.9),
     (3.2, 0.8), (3.9, 1.0), (4.4, -0.7)]
  let q : Float × Float := (-0.8, 0)
  let crossPts : List (Float × Float × Int) :=
    [(0.35, 0, 1), (1.72, 0, -1), (2.92, 0, 1), (4.16, 0, -1)]
  ov <|
    [seg u q (5.0, 0) (dashed ink), dot u q ink 3.6,
     polyOpen u wave { color := accent, width := 2.0 }] ++
    (crossPts.flatMap fun (x, y, s) =>
      [dot u (x, y) (if s == 1 then leaf else crimson) 3.6,
       lbl u (x, y - 0.4) (if s == 1 then "+1" else "−1")
         (if s == 1 then leaf else crimson) 12 (italic := false)]) ++
    [lbl u (2.2, 1.45) "one loop ⇒ signs must alternate" ink 13]

/-! ## Figure 8 — the Maehara construction (continuous JCT, Step A) -/

def maeharaFigure : Fig :=
  let u := 78.0
  let a : Float × Float := (-1, 0)
  let b : Float × Float := (1, 0)
  -- axis points: l (top of J_n), m (lowest point of J_n on the axis),
  -- z₀ (midpoint of p,m), p (top of J_s below m), q (bottom of J_s)
  let l : Float × Float := (0, 1.5)
  let m : Float × Float := (0, 0.55)
  let z₀ : Float × Float := (0, 0.125)
  let p : Float × Float := (0, -0.3)
  let q : Float × Float := (0, -1.45)
  -- J_n: a → l → dip to m → b   (upper arc, wiggly)
  let Jn : List (Float × Float) :=
    [a, (-0.75, 0.75), (-0.45, 1.3), l, (0.45, 1.25), (0.62, 0.85), m,
     (0.55, 0.42), (0.8, 0.28), b]
  -- J_s: a → p → q → b   (lower arc)
  let Js : List (Float × Float) :=
    [a, (-0.55, -0.5), (-0.25, -0.28), p, (0.4, -0.55), (0.15, -1.0), q,
     (0.6, -1.1), (0.85, -0.5), b]
  -- the bottom→top path of Step A (low case): s → w → z₀ → m → l → n
  let w : Float × Float := (-1, -0.85)
  let path : List (Float × Float) :=
    [(0, -2), (-0.55, -1.9), (-0.93, -1.5), w,          -- s → w through the lower boundary region
     (-0.75, -0.7), (-0.5, -0.2), (-0.3, 0.05), z₀]     -- w → z₀ along the escaping path
  ov <|
    [ -- rectangle E
      polyClosed u [(-1, -2), (1, -2), (1, 2), (-1, 2)] noFill { color := gray, width := 1.3 },
      -- the axis
      seg u (0, -2) (0, 2) (dashed grayFaint),
      -- the two arcs
      polyOpen u Jn { color := accent, width := 2.2 },
      polyOpen u Js { color := crimson, width := 2.2 },
      -- Step-A path (green): s → w → z₀, then z₀ → m → l → n up the axis / J_n
      polyOpen u path { color := leaf, width := 2.0 },
      seg u z₀ m { color := leaf, width := 2.0 },
      polyOpen u [m, (0.62, 0.85), (0.45, 1.25), l] { color := leaf, width := 2.0 },
      seg u l (0, 2) { color := leaf, width := 2.0 }
    ] ++
    [dot u a ink 4.0, dot u b ink 4.0,
     dot u l accent 3.6, dot u m accent 3.6, dot u z₀ crimson 4.0,
     dot u p crimson 3.6, dot u q crimson 3.6, dot u w leaf 3.8] ++
    [lbl u (-1.12, 0) "a" ink, lbl u (1.1, 0) "b" ink,
     lbl u (0.14, 1.55) "l" accent, lbl u (0.14, 0.62) "m" accent,
     lbl u (0.16, 0.1) "z₀" crimson,
     lbl u (0.14, -0.38) "p" crimson, lbl u (0.15, -1.5) "q" crimson,
     lbl u (-0.87, -0.87) "w" leaf,
     lbl u (-0.55, 1.5) "Jₙ" accent 15, lbl u (-0.5, -0.95) "Jₛ" crimson 15,
     lbl u (0.12, -1.93) "s" leaf, lbl u (0.12, 1.9) "n" leaf]

/-! ## Figure 9 — the crossing lemma -/

def crossingFigure : Fig :=
  let u := 60.0
  let h : List (Float × Float) :=
    [(-1, 0.3), (-0.4, 0.7), (0.2, -0.2), (0.7, 0.5), (1, 0.1)]
  let v : List (Float × Float) :=
    [(0.15, -1), (-0.3, -0.4), (0.4, 0.25), (0.05, 0.6), (0.25, 1)]
  ov
    [ polyClosed u [(-1, -1), (1, -1), (1, 1), (-1, 1)] noFill { color := gray, width := 1.3 },
      polyOpen u h { color := accent, width := 2.2 },
      polyOpen u v { color := crimson, width := 2.2 },
      dot u (0.28, 0.08) ink 4.5,
      lbl u (0.52, -0.08) "must meet" ink 13,
      lbl u (-1.13, 0.3) "h" accent, lbl u (0.15, -1.13) "v" crimson
    ]

/-! ## Figure 10 — Brouwer via ray retraction -/

def brouwerFigure : Fig :=
  let u := 60.0
  let x : Float × Float := (0.15, 0.2)
  let fx : Float × Float := (-0.3, -0.25)
  -- r(x): the ray from f(x) through x, extended to the unit circle
  let r : Float × Float := (0.716, 0.766)
  ov
    [ Diagram.circle u (fill := accentFill) (stroke := { color := accent, width := 1.8 }),
      seg u fx r { color := ink, width := 1.4 },
      dot u fx crimson 4.0, dot u x ink 4.0, dot u r leaf 4.5,
      lbl u (-0.42, -0.38) "f x" crimson,
      lbl u (0.18, 0.34) "x" ink,
      lbl u (0.9, 0.85) "r x" leaf,
      lbl u (0, -1.25) "no fixed point ⇒ a retraction onto the boundary" ink 13
    ]

end Site.Figures
