module

public import ArtGallery.Orthogonal.BoundaryPoint.AdditionGap
public import ArtGallery.Orthogonal.BoundaryPoint.ChimneyMouth
public import ArtGallery.Orthogonal.BoundaryPoint.CriticalOwnership
public import ArtGallery.Orthogonal.BoundaryPoint.RoomRelation.Lower
public import ArtGallery.Orthogonal.BoundaryPoint.RoomForeign.Lower

/-! Continuum soundness for the actual addition triangle of the generated room. -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.RoomSound.Lower
open RoomFamily.Lower RoomRelation.Lower RoomCoordinates RoomPolynomials InverseGap
open AxisBlock AdditionGap SlotLines RoomGrid Geometry ArtGallery.Orthogonal.Hard DerivedAlgebra
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000

noncomputable def spot (s : ℝ) (i : Nat) : Set Point :=
  let f := gridPt (xAxis.coordsR s) (yAxis.coordsR s)
  ArtGallery.segment (f (RoomExclusion.nodeAt roles i 1)) (f (RoomExclusion.nodeAt roles i 2))

def OnSpots (s : ℝ) (G : Nat → Point) := ∀ i, i<7 → G i∈spot s i
def critical (z : Point) : Prop :=
  (867≤z.1 ∧ z.1≤869 ∧ 49/100≤z.2 ∧ z.2≤51/100) ∨ (1438≤z.1 ∧ z.1≤1440 ∧ 11/5≤z.2 ∧ z.2≤221/100)
def CoversCritical (n : Nat) (G : Nat → Point) := ∀ z∈(room n).filled, critical z → ∃ i, i<7 ∧ (room n).Sees (G i) z

theorem box_fits : fits xAxis yAxis [867] [869] [49/100] [51/100] (24,35,10,15)=true := by decide +kernel
theorem box_member : (24,35,10,15)∈cells := by decide +kernel

def xQ : AxisBlock.Query := ⟨5,([766],[0]),[867],[2/5],[3/5],true,false,true⟩
theorem x_check : ok xAxis yAxis cells roles xQ=true := by decide +kernel

private theorem x_at (n : Nat) (hn : 65≤n) (g : Point) (hg : g∈spot (1/n) 5) (Y : ℝ)
    (hl : 2/5≤Y) (hu : Y≤3/5) (vis : (room n).Sees g (867,Y)) :
    Y≤rayY g (766,0) 867 := by
  let s : ℝ := 1/n
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have pos : 0<s := by dsimp [s]; positivity
  have cap := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<65) hn'
  have src : g∈ArtGallery.segment (pt s ((ends xAxis yAxis roles xQ.role).getD 0 ([],[])))
      (pt s ((ends xAxis yAxis roles xQ.role).getD 1 ([],[]))) := by
    change g∈ArtGallery.segment (pt s (polyNode xAxis yAxis (RoomExclusion.nodeAt roles 5 1)))
      (pt s (polyNode xAxis yAxis (RoomExclusion.nodeAt roles 5 2)))
    simpa only [node_value,spot,s] using hg
  have left : evalR s xQ.bottom≤Y := by simpa [xQ,evalR] using hl
  have right : Y≤evalR s xQ.top := by simpa [xQ,evalR] using hu
  have tar := target (a:=xQ.axis) left right
  have H := AxisBlock.sound pos cap (RoomFill.Lower.filled_eq n hn) x_check src tar
    (by simpa [xQ,evalR] using vis)
  simpa [xQ,pt,evalR] using H

def rQ : AxisBlock.Query := ⟨4,([(2639/2)],[0]),[869],[2/5],[3/5],false,false,false⟩
theorem r_check : ok xAxis yAxis cells roles rQ=true := by decide +kernel

private theorem r_at (n : Nat) (hn : 65≤n) (g : Point) (hg : g∈spot (1/n) 4) (Y : ℝ)
    (hl : 2/5≤Y) (hu : Y≤3/5) (vis : (room n).Sees g (869,Y)) :
    rayY g ((2639/2),0) 869≤Y := by
  let s : ℝ := 1/n
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have pos : 0<s := by dsimp [s]; positivity
  have cap := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<65) hn'
  have src : g∈ArtGallery.segment (pt s ((ends xAxis yAxis roles rQ.role).getD 0 ([],[])))
      (pt s ((ends xAxis yAxis roles rQ.role).getD 1 ([],[]))) := by
    change g∈ArtGallery.segment (pt s (polyNode xAxis yAxis (RoomExclusion.nodeAt roles 4 1)))
      (pt s (polyNode xAxis yAxis (RoomExclusion.nodeAt roles 4 2)))
    simpa only [node_value,spot,s] using hg
  have left : evalR s rQ.bottom≤Y := by simpa [rQ,evalR] using hl
  have right : Y≤evalR s rQ.top := by simpa [rQ,evalR] using hu
  have tar := target (a:=rQ.axis) left right
  have H := AxisBlock.sound pos cap (RoomFill.Lower.filled_eq n hn) r_check src tar
    (by simpa [rQ,evalR] using vis)
  simpa [rQ,pt,evalR] using H

def zQ : AxisBlock.Query := ⟨6,([(1655/2)],[0]),[867],[2/5],[3/5],true,true,false⟩
theorem z_check : ok xAxis yAxis cells roles zQ=true := by decide +kernel

private theorem z_at (n : Nat) (hn : 65≤n) (g : Point) (hg : g∈spot (1/n) 6) (Y : ℝ)
    (hl : 2/5≤Y) (hu : Y≤3/5) (vis : (room n).Sees g (867,Y)) :
    rayY g ((1655/2),0) 867≤Y := by
  let s : ℝ := 1/n
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have pos : 0<s := by dsimp [s]; positivity
  have cap := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<65) hn'
  have src : g∈ArtGallery.segment (pt s ((ends xAxis yAxis roles zQ.role).getD 0 ([],[])))
      (pt s ((ends xAxis yAxis roles zQ.role).getD 1 ([],[]))) := by
    change g∈ArtGallery.segment (pt s (polyNode xAxis yAxis (RoomExclusion.nodeAt roles 6 1)))
      (pt s (polyNode xAxis yAxis (RoomExclusion.nodeAt roles 6 2)))
    simpa only [node_value,spot,s] using hg
  have left : evalR s zQ.bottom≤Y := by simpa [zQ,evalR] using hl
  have right : Y≤evalR s zQ.top := by simpa [zQ,evalR] using hu
  have tar := target (a:=zQ.axis) left right
  have H := AxisBlock.sound pos cap (RoomFill.Lower.filled_eq n hn) z_check src tar
    (by simpa [zQ,evalR] using vis)
  simpa [zQ,pt,evalR] using H

private theorem three (n : Nat) (hn : 65≤n) (G : Nat → Point)
    (pins : OnSpots (1/n) G) (cover : CoversCritical n G) (X Y : ℝ)
    (lx : 867≤X) (rx : X≤869) (ly : 49/100≤Y) (ry : Y≤51/100) :
    (room n).Sees (G 5) (X,Y) ∨ (room n).Sees (G 4) (X,Y) ∨ (room n).Sees (G 6) (X,Y) := by
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have pos : 0<(1:ℝ)/n := by positivity
  have H := free_box pos (one_div_le_one_div_of_le (by norm_num) hn') (RoomFill.Lower.filled_eq n hn)
    box_member box_fits X Y (by simpa [evalR] using lx) (by simpa [evalR] using rx)
      (by simpa [evalR] using ly) (by simpa [evalR] using ry)
  obtain ⟨i,hi,seen⟩ := cover _ H (Or.inl ⟨lx,rx,ly,ry⟩)
  interval_cases i

  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test1 (by simp [RoomForeign.Lower.tests]) _ (pins 0 (by decide))
      (X,Y) (by norm_num [RoomForeign.Lower.test1]; exact lx) (by norm_num [RoomForeign.Lower.test1]; exact rx)
        (by norm_num [RoomForeign.Lower.test1]; exact ly) (by norm_num [RoomForeign.Lower.test1]; exact ry)) seen).elim

  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test2 (by simp [RoomForeign.Lower.tests]) _ (pins 1 (by decide))
      (X,Y) (by norm_num [RoomForeign.Lower.test2]; exact lx) (by norm_num [RoomForeign.Lower.test2]; exact rx)
        (by norm_num [RoomForeign.Lower.test2]; exact ly) (by norm_num [RoomForeign.Lower.test2]; exact ry)) seen).elim

  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test0 (by simp [RoomForeign.Lower.tests]) _ (pins 2 (by decide))
      (X,Y) (by norm_num [RoomForeign.Lower.test0]; exact lx) (by norm_num [RoomForeign.Lower.test0]; exact rx)
        (by norm_num [RoomForeign.Lower.test0]; exact ly) (by norm_num [RoomForeign.Lower.test0]; exact ry)) seen).elim

  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test6 (by simp [RoomForeign.Lower.tests]) _ (pins 3 (by decide))
      (X,Y) (by norm_num [RoomForeign.Lower.test6]; exact lx) (by norm_num [RoomForeign.Lower.test6]; exact rx)
        (by norm_num [RoomForeign.Lower.test6]; exact ly) (by norm_num [RoomForeign.Lower.test6]; exact ry)) seen).elim

  · exact Or.inr (Or.inl seen)
  · exact Or.inl seen
  · exact Or.inr (Or.inr seen)

theorem triangle_forces (n : Nat) (hn : 65≤n) (G : Nat → Point)
    (pins : OnSpots (1/n) G) (cover : CoversCritical n G) (tx tr tz : ℝ)
    (hx : 0≤tx ∧ tx≤3/2) (hr : 0≤tr ∧ tr≤3/2) (hz : 0≤tz ∧ tz≤3/2)
    (gx : G 5=guard (1/n) 5 tx) (gr : G 4=guard (1/n) 4 tr) (gz : G 6=guard (1/n) 6 tz) :
    tz≤tx+tr+(-3/2) := by
  let s : ℝ := 1/n
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have pos : 0<s := by dsimp [s]; positivity
  have small : s≤1 := (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<65) hn').trans (by norm_num)
  have pow : s^2≤1 := by nlinarith [mul_le_mul small small pos.le (by norm_num : (0:ℝ)≤1)]
  have bounded (t : ℝ) (ht : 0≤t ∧ t≤3/2) : 0≤t*s^2 ∧ t*s^2≤2 :=
    ⟨mul_nonneg ht.1 (sq_nonneg s), (mul_le_mul ht.2 pow (sq_nonneg s) (by norm_num)).trans (by norm_num)⟩
  let bx := xSlope 766 (G 5)
  let br := xSlope (2639/2) (G 4)
  let bz := xSlope (1655/2) (G 6)
  change G 5=guard s 5 tx at gx
  change G 4=guard s 4 tr at gr
  change G 6=guard s 6 tz at gz

  have loc_x : ((G 5).1≤700) ∧ -3≤(G 5).2 ∧ (G 5).2<0 := by
    rw [gx,position_x]
    norm_num [evalR] <;> nlinarith only [(bounded tx hx).1,(bounded tx hx).2,sq_nonneg s,pow]

  have loc_r : (1400≤(G 4).1) ∧ -3≤(G 4).2 ∧ (G 4).2<0 := by
    rw [gr,position_r]
    norm_num [evalR] <;> nlinarith only [(bounded tr hr).1,(bounded tr hr).2,sq_nonneg s,pow]

  have loc_z : ((G 6).1≤700) ∧ -3≤(G 6).2 ∧ (G 6).2<0 := by
    rw [gz,position_z]
    norm_num [evalR] <;> nlinarith only [(bounded tz hz).1,(bounded tz hz).2,sq_nonneg s,pow]

  have b_x : 2039/10≤bx ∧ bx≤2041/10 := by
    dsimp only [bx,xSlope]; rw [gx,position_x]
    norm_num [evalR] <;> first | (constructor <;> nlinarith only [(bounded tx hx).1,(bounded tx hx).2,sq_nonneg s,pow]) | nlinarith only [(bounded tx hx).1,(bounded tx hx).2,sq_nonneg s,pow]

  have b_r : -9031/10≤br ∧ br≤ -9029/10 := by
    dsimp only [br,xSlope]; rw [gr,position_r]
    norm_num [evalR] <;> first | (constructor <;> nlinarith only [(bounded tr hr).1,(bounded tr hr).2,sq_nonneg s,pow]) | nlinarith only [(bounded tr hr).1,(bounded tr hr).2,sq_nonneg s,pow]

  have b_z : 0<bz := by
    dsimp only [bz,xSlope]; rw [gz,position_z]
    norm_num [evalR] <;> first | (constructor <;> nlinarith only [(bounded tz hz).1,(bounded tz hz).2,sq_nonneg s,pow]) | nlinarith only [(bounded tz hz).1,(bounded tz hz).2,sq_nonneg s,pow]

  have residual : (8*bx+br)/9-bz≤0 := by
    apply triangle b_x b_r
    intro X Y lx rx ly ry
    rcases three n hn G pins cover X Y lx rx ly ry with h|h|h

    · have HH := box_transfer (c:=((766:ℝ),0)) false true
        (by change (G 5).1≤767; linarith [loc_x.1]) ⟨loc_x.2.1,loc_x.2.2.le⟩
        lx rx ly ry (x_at n hn _ (pins 5 (by decide))) h
      have line := slope_line (g:=G 5) 766 X loc_x.2.2.ne (by intro E; linarith [loc_x.1])
      change bx*rayY (G 5) _ X=X-766 at line

      left; nlinarith only [line,mul_le_mul_of_nonneg_left HH (by linarith [b_x.1] : 0≤bx)]

    · have HH := box_transfer (c:=(((2639/2):ℝ),0)) true false
        (by change 969≤(G 4).1; linarith [loc_r.1]) ⟨loc_r.2.1,loc_r.2.2.le⟩
        lx rx ly ry (r_at n hn _ (pins 4 (by decide))) h
      have line := slope_line (g:=G 4) (2639/2) X loc_r.2.2.ne (by intro E; linarith [loc_r.1])
      change br*rayY (G 4) _ X=X-(2639/2) at line

      right; left; nlinarith only [line,mul_le_mul_of_nonpos_left HH (by linarith [b_r.2] : br≤0)]

    · have HH := box_transfer (c:=(((1655/2):ℝ),0)) false false
        (by change (G 6).1≤767; linarith [loc_z.1]) ⟨loc_z.2.1,loc_z.2.2.le⟩
        lx rx ly ry (z_at n hn _ (pins 6 (by decide))) h
      have line := slope_line (g:=G 6) (1655/2) X loc_z.2.2.ne (by intro E; linarith [loc_z.1])
      change bz*rayY (G 6) _ X=X-(1655/2) at line

      right; right; nlinarith only [line,mul_le_mul_of_nonneg_left HH b_z.le]

  have identity := balance s tx tr tz
  change (8*xSlope 766 (guard s 5 tx)+xSlope (2639/2) (guard s 4 tr))/9-xSlope (1655/2) (guard s 6 tz)=_ at identity
  rw [← gx,← gr,← gz] at identity
  change (8*bx+br)/9-bz=_ at identity
  have positive : 0<(4/3:ℝ)*(s^2/50050) := by positivity
  have sign := nonpos_of_mul_nonpos_right (identity ▸ residual) positive
  linarith

theorem mouth_ok : ChimneyMouth.check xAxis yAxis cells (31,32,22,23) (50352/35) (100739/70) (11/5) (19834298/9008765)=true := by decide +kernel
theorem mouth_fits : fits xAxis yAxis [(50352/35)] [(100739/70)] [(11/5)] [(19834298/9008765)] (31,32,22,23)=true := by decide +kernel
theorem mouth_member : (31,32,22,23)∈cells := by decide +kernel

private theorem top_pair (n : Nat) (hn : 65≤n) (G : Nat → Point) (pins : OnSpots (1/n) G)
    (cover : CoversCritical n G) (X : ℝ) (xl : (50352/35)≤X) (xr : X≤(100739/70)) :
    (room n).Sees (G 3) (X,(19834298/9008765)) ∨ (room n).Sees (G 4) (X,(19834298/9008765)) := by
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have hs : 0<(1:ℝ)/n := by positivity
  have H := free_box hs (one_div_le_one_div_of_le (by norm_num) hn') (RoomFill.Lower.filled_eq n hn)
    mouth_member mouth_fits X (19834298/9008765) (by simpa [evalR] using xl) (by simpa [evalR] using xr)
      (by norm_num [evalR]) (by norm_num [evalR])
  have L : 1438≤X := by linarith
  have R : X≤1440 := by linarith
  obtain ⟨i,hi,seen⟩ := cover _ H (Or.inr ⟨L,R,by norm_num,by norm_num⟩)
  interval_cases i
  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test4 (by simp [RoomForeign.Lower.tests]) _ (pins 0 (by decide))
      (X,(19834298/9008765)) (by norm_num [RoomForeign.Lower.test4]; exact L) (by norm_num [RoomForeign.Lower.test4]; exact R)
        (by norm_num [RoomForeign.Lower.test4]) (by norm_num [RoomForeign.Lower.test4])) seen).elim
  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test5 (by simp [RoomForeign.Lower.tests]) _ (pins 1 (by decide))
      (X,(19834298/9008765)) (by norm_num [RoomForeign.Lower.test5]; exact L) (by norm_num [RoomForeign.Lower.test5]; exact R)
        (by norm_num [RoomForeign.Lower.test5]) (by norm_num [RoomForeign.Lower.test5])) seen).elim
  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test3 (by simp [RoomForeign.Lower.tests]) _ (pins 2 (by decide))
      (X,(19834298/9008765)) (by norm_num [RoomForeign.Lower.test3]; exact L) (by norm_num [RoomForeign.Lower.test3]; exact R)
        (by norm_num [RoomForeign.Lower.test3]) (by norm_num [RoomForeign.Lower.test3])) seen).elim
  · exact Or.inl seen
  · exact Or.inr seen
  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test7 (by simp [RoomForeign.Lower.tests]) _ (pins 5 (by decide))
      (X,(19834298/9008765)) (by norm_num [RoomForeign.Lower.test7]; exact L) (by norm_num [RoomForeign.Lower.test7]; exact R)
        (by norm_num [RoomForeign.Lower.test7]) (by norm_num [RoomForeign.Lower.test7])) seen).elim
  · exact ((RoomForeign.Lower.exclude n hn RoomForeign.Lower.test8 (by simp [RoomForeign.Lower.tests]) _ (pins 6 (by decide))
      (X,(19834298/9008765)) (by norm_num [RoomForeign.Lower.test8]; exact L) (by norm_num [RoomForeign.Lower.test8]; exact R)
        (by norm_num [RoomForeign.Lower.test8]) (by norm_num [RoomForeign.Lower.test8])) seen).elim

theorem relay_forces (n : Nat) (hn : 65≤n) (G : Nat → Point) (pins : OnSpots (1/n) G) (cover : CoversCritical n G)
    (tq tr : ℝ) (hq : 0≤tq ∧ tq≤3/2) (hr : 0≤tr ∧ tr≤3/2)
    (gq : G 3=guard (1/n) 3 tq) (gr : G 4=guard (1/n) 4 tr) : tr≤tq := by
  let s : ℝ := 1/n
  have hn' : (65:ℝ)≤n := by exact_mod_cast hn
  have hs : 0<s := by dsimp [s]; positivity
  have hu : s≤1/65 := one_div_le_one_div_of_le (by norm_num) hn'
  have small : s≤1 := hu.trans (by norm_num)
  have pow : s^2≤1 := by nlinarith [mul_le_mul small small hs.le (by norm_num : (0:ℝ)≤1)]
  have bounded (u : ℝ) (h : 0≤u ∧ u≤3/2) : 0≤u*s^2 ∧ u*s^2≤2 :=
    ⟨mul_nonneg h.1 (sq_nonneg s),(mul_le_mul h.2 pow (sq_nonneg s) (by norm_num)).trans (by norm_num)⟩
  have filled := RoomFill.Lower.filled_eq n hn
  change G 3=guard s 3 tq at gq
  change G 4=guard s 4 tr at gr
  let Q := ChimneyMouth.upperX (G 3) (50352/35) (11/5) (19834298/9008765)
  let R := ChimneyMouth.upperX (G 4) (100739/70) (11/5) (19834298/9008765)
  have idQ : Q=90753307696/63061355-(27/1171139450)*tq*s^2 := by
    dsimp only [Q,ChimneyMouth.upperX]; rw [gq,position_q]
    norm_num [evalR] <;> ring
  have idR : R=90753307696/63061355-(27/1171139450)*tr*s^2 := by
    dsimp only [R,ChimneyMouth.upperX]; rw [gr,position_r]
    norm_num [evalR] <;> ring
  have qB : (50352/35)≤Q ∧ Q≤(100739/70) := by rw [idQ]; constructor <;> nlinarith only [(bounded tq hq).1,(bounded tq hq).2]
  have rB : (50352/35)≤R ∧ R≤(100739/70) := by rw [idR]; constructor <;> nlinarith only [(bounded tr hr).1,(bounded tr hr).2]
  have qFloor : (G 3).2<(11/5) := by rw [gq,position_q]; norm_num
  have rFloor : (G 4).2<(11/5) := by rw [gr,position_r]; norm_num
  have ord : Q≤R := by
    apply ChimneyMouth.gap qB rB
    intro X xl xr
    rcases top_pair n hn G pins cover X xl xr with a|h
    · left
      have ray := ChimneyMouth.window hs hu filled mouth_member mouth_ok (g:=G 3) (by norm_num)
        (by norm_num; exact qFloor) (X:=X) (by norm_num; exact xl) (by norm_num; exact xr)
        (by norm_num; exact a)
      simpa [Q] using ray.1
    · right
      have ray := ChimneyMouth.window hs hu filled mouth_member mouth_ok (g:=G 4) (by norm_num)
        (by norm_num; exact rFloor) (X:=X) (by norm_num; exact xl) (by norm_num; exact xr)
        (by norm_num; exact h)
      simpa [R] using ray.2
  rw [idQ,idR] at ord
  by_contra! rev
  nlinarith only [ord,mul_pos (sub_pos.mpr rev) (sq_pos_of_pos hs)]

theorem forces (n : Nat) (hn : 65≤n) (G : Nat → Point)
    (pins : OnSpots (1/n) G) (cover : CoversCritical n G) (tq tr tx tz : ℝ)
    (hq : 0≤tq ∧ tq≤3/2) (hr : 0≤tr ∧ tr≤3/2) (hx : 0≤tx ∧ tx≤3/2) (hz : 0≤tz ∧ tz≤3/2)
    (gq : G 3=guard (1/n) 3 tq) (gr : G 4=guard (1/n) 4 tr)
    (gx : G 5=guard (1/n) 5 tx) (gz : G 6=guard (1/n) 6 tz) : tz≤tx+tq+(-3/2) := by
  linarith only [triangle_forces n hn G pins cover tx tr tz hx hr hz gx gr gz,
    relay_forces n hn G pins cover tq tr hq hr gq gr]

theorem spot_marks (i : Fin 7) : (RoomExclusion.nodeAt roles i 1, RoomExclusion.nodeAt roles i 2) ∈
    GridPins.requirements roles := by fin_cases i <;> decide +kernel

theorem joined_forces (n : Nat) (hn : 65≤n) (P : Polygon) (tree : WindowTree.Attachments (room n).filled P.filled)
    (H : Set Point) (G : Nat → Point) (pins : OnSpots (1/n) G)
    (cover : ∀ z∈P.filled, ∃ g∈H, P.Sees g z)
    (foreign : ∀ z∈(room n).filled, critical z → ∀ g∈H, (∀ i, i<7 → g≠G i) → ¬P.Sees g z)
    (tq tr tx tz : ℝ) (hq : 0≤tq ∧ tq≤3/2) (hr : 0≤tr ∧ tr≤3/2)
    (hx : 0≤tx ∧ tx≤3/2) (hz : 0≤tz ∧ tz≤3/2)
    (gq : G 3=guard (1/n) 3 tq) (gr : G 4=guard (1/n) 4 tr)
    (gx : G 5=guard (1/n) 5 tx) (gz : G 6=guard (1/n) 6 tz) : tz≤tx+tq+(-3/2) := by
  have actors (i : Nat) (hi : i<7) : G i∈(room n).filled :=
    Or.inl (guards_and_witnesses_on_boundary n hn _ (spot_marks ⟨i,hi⟩) (pins i hi))
  exact forces n hn G pins (CriticalOwnership.restrict_to_room tree critical H 7 G actors cover foreign)
    tq tr tx tz hq hr hx hz gq gr gx gz

end ArtGallery.Orthogonal.BoundaryPoint.RoomSound.Lower
end
