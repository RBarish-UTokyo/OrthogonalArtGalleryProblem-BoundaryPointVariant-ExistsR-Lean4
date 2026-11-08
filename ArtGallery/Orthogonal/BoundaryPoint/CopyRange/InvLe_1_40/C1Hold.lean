module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.InvLe_1_40
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1Defs
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S0
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S1
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S2
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S3
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S4
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S5
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40.C1S6

/-! Range data of profile `InvLe_1_40`: `C1Hold` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.InvLe_1_40
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- @@HOLD c1

/-- Closed forms of the registers of channel 1, step by step. -/
theorem c1hold {args xs : List ℚ} (m : Model args xs rows boxes cache) {x y z : ℝ}
    (hin : ∀ k Q d, (k,Q,d)∈c1ins → ((getRat args k : ℚ) : ℝ)*d=Ex.ev x y z Q)
    (B : PolyBox.Box (1/65:ℚ) (199/5005:ℚ) (797/18590:ℚ) x y z) :
    ∀ t∈c1tops, RegCert.Holds xs x y z t.1 t.2.1 t.2.2 := by
  have h861 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k861
  have h860 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k860
  have h858 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k858
  have h857 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f861]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k857
  have h856 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k856
  have h855 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f856]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k855
  have h854 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f857,c1f855]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k854
  have h853 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k853
  have h852 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f853]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k852
  have h851 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k851
  have h850 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f851]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k850
  have h846 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f852]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k846
  have h845 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k845
  have h844 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f846,c1f845]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k844
  have h843 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f844]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k843
  have h842 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k842
  have h841 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f843,c1f842]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k841
  have h840 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k840
  have h836 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k836
  have h835 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f861,c1f836]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k835
  have h834 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f860,c1f835]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k834
  have h832 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k832
  have h831 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f832]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k831
  have h830 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f861,c1f831]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k830
  have h829 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k829
  have h828 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f861,c1f829]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k828
  have h827 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k827
  have h826 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k826
  have h825 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f827,c1f826]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k825
  have h817 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k817
  have h816 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f817]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k816
  have h815 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f830]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k815
  have h813 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f816]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k813
  have h812 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k812
  have h811 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f813,c1f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k811
  have h810 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f811]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k810
  have h807 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k807
  have h797 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k797
  have h796 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f828,c1f797]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k796
  have h790 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k790
  have h789 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f790]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k789
  have h787 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k787
  have h785 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k785
  have h784 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f785]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k784
  have h782 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k782
  have h781 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f787,c1f782]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k781
  have h780 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f781]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k780
  have h777 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k777
  have h775 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k775
  have h774 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f828,c1f775]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k774
  have h773 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f785,c1f774]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k773
  have h757 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k757
  have h747 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f787]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k747
  have h739 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f747]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k739
  have h738 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f739]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k738
  have h737 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f738]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k737
  have h684 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k684
  have h683 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f684]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k683
  have h661 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f775]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k661
  have h607 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f790]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k607
  have h606 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f607]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k606
  have h604 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k604
  have h603 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f604]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k603
  have h602 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f603]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k602
  have h574 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f858,c1f840]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k574
  have h573 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k573
  have h572 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f574,c1f573]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k572
  have h571 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f834,c1f572]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k571
  have h570 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k570
  have h569 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f570]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k569
  have h568 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f569]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k568
  have h567 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f825,c1f568]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k567
  have h566 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f571,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k566
  have h565 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f566]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k565
  have h564 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f565]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k564
  have h563 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f815,c1f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k563
  have h562 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f810,c1f563]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k562
  have h561 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f817,c1f562]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k561
  have h560 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f807,c1f561]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k560
  have h559 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k559
  have h558 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f817,c1f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k558
  have h557 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f558]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k557
  have h556 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f557]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k556
  have h555 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f559,c1f556]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k555
  have h554 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f810,c1f555]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k554
  have h553 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f554]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k553
  have h552 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f560,c1f553]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k552
  have h551 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f796,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k551
  have h548 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f552,c1f551]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k548
  have h547 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f850,c1f548]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k547
  have h546 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f789]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k546
  have h545 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f787,c1f546]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k545
  have h544 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f784,c1f545]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k544
  have h543 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f780,c1f544]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k543
  have h542 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f543]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k542
  have h541 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f777,c1f542]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k541
  have h540 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f812]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k540
  have h539 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f540]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k539
  have h538 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f773,c1f539]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k538
  have h537 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f567,c1f538]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k537
  have h536 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f780,c1f537]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k536
  have h535 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f536]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k535
  have h534 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f541,c1f535]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k534
  have h533 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k533
  have h532 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k532
  have h531 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f533,c1f532]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k531
  have h530 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f534,c1f533]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k530
  have h529 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f543]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k529
  have h528 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f530,c1f529]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k528
  have h525 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f757,c1f528]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k525
  have h524 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f531,c1f525]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k524
  have h523 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f850,c1f524]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k523
  have h522 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f789,c1f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k522
  have h521 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f523,c1f522]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k521
  have h520 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f521]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k520
  have h519 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f551,c1f520]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k519
  have h518 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f533,c1f519]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k518
  have h517 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f850,c1f518]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k517
  have h516 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k516
  have h515 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f787,c1f569]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k515
  have h514 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f516,c1f515]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k514
  have h513 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f747,c1f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k513
  have h512 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f567,c1f513]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k512
  have h511 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f512]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k511
  have h510 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f514,c1f511]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k510
  have h509 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f737,c1f510]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k509
  have h508 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f547]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k508
  have h507 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f508]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k507
  have h506 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f509,c1f507]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k506
  have h501 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f523]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k501
  have h500 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f567,c1f501]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k500
  have h499 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f506]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k499
  have h498 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f500,c1f499]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k498
  have h497 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f517]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k497
  have h496 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f517,c1f498]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k496
  have h495 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f496]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k495
  have h494 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f523,c1f495]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k494
  have h493 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f571,c1f523]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k493
  have h492 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f493]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k492
  have h491 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f815,c1f492]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k491
  have h490 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f854,c1f500]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k490
  have h489 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f490]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k489
  have h488 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f489]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k488
  have h487 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f491,c1f488]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k487
  have h486 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f487]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k486
  have h485 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f571,c1f486]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k485
  have h484 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f494]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k484
  have h483 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f497,c1f484]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k483
  have h482 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f827,c1f483]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k482
  have h481 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f787,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k481
  have h480 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f494]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k480
  have h479 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f481,c1f480]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k479
  have h478 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f479]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k478
  have h477 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f482,c1f478]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k477
  have h476 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f477]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k476
  have h475 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f747,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k475
  have h474 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f787,c1f475]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k474
  have h473 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f569,c1f474]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k473
  have h472 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f737,c1f473]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k472
  have h471 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f841,c1f523]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k471
  have h470 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f471]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k470
  have h469 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f470]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k469
  have h468 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f469]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k468
  have h467 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f472,c1f468]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k467
  have h466 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f500,c1f477]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k466
  have h465 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f466]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k465
  have h464 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f467,c1f465]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k464
  have h463 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f499,c1f464]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k463
  have h462 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f517,c1f463]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k462
  have h461 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f485]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k461
  have h460 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f476,c1f461]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k460
  have h459 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f460]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k459
  have h458 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f462,c1f459]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k458
  have h457 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f683,c1f488]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k457
  have h456 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f683,c1f478]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k456
  have h455 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f476,c1f456]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k455
  have h454 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f485,c1f457]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k454
  have h451 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f463,c1f457]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k451
  have h450 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f498,c1f485]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k450
  have h449 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f450]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k449
  have h448 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f449]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k448
  have h447 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f456,c1f448]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k447
  have h446 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f447]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k446
  have h445 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f451,c1f446]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k445
  have h444 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f517,c1f445]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k444
  have h443 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f461,c1f455]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k443
  have h442 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f457]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k442
  have h441 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f443,c1f442]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k441
  have h440 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f460,c1f441]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k440
  have h439 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f440]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k439
  have h438 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f444,c1f439]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k438
  have h437 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f458,c1f438]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k437
  have h436 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f661,c1f478]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k436
  have h435 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f476,c1f436]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k435
  have h433 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f448,c1f436]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k433
  have h432 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f433]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k432
  have h431 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f451,c1f432]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k431
  have h430 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f517,c1f431]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k430
  have h429 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f461,c1f435]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k429
  have h428 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f442,c1f429]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k428
  have h427 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f460,c1f428]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k427
  have h426 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f427]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k426
  have h425 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f430,c1f426]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k425
  have h424 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f458,c1f425]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k424
  have h423 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f789,c1f488]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k423
  have h422 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f485,c1f423]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k422
  have h419 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f463,c1f423]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k419
  have h418 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f446,c1f419]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k418
  have h417 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f517,c1f418]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k417
  have h416 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f423]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k416
  have h415 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f443,c1f416]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k415
  have h414 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f460,c1f415]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k414
  have h413 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f414]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k413
  have h412 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f417,c1f413]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k412
  have h411 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f458,c1f412]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k411
  have h409 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f432,c1f419]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k409
  have h408 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f517,c1f409]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k408
  have h407 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f429,c1f416]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k407
  have h406 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f460,c1f407]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k406
  have h405 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f406]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k405
  have h404 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f408,c1f405]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k404
  have h403 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f458,c1f404]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k403
  have h385 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f606,c1f571]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k385
  have h384 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f602,c1f385]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k384
  have h383 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f496,c1f458]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k383
  have h382 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f384,c1f383]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k382
  have h381 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f382]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k381
  have h368 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f812,c1f567]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k368
  have h306 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k306
  have h301 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f454,c1f437]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k301
  have h300 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f301]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k300
  have h299 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f300]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k299
  have h298 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f454,c1f424]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k298
  have h297 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f298]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k297
  have h296 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f297]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k296
  have h295 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f422,c1f411]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k295
  have h294 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f295]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k294
  have h293 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f294]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k293
  have h292 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f422,c1f403]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k292
  have h291 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f292]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k291
  have h290 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f547,c1f291]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k290
  have h289 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f299,c1f296]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k289
  have h288 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f293,c1f289]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k288
  have h287 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f290,c1f288]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k287
  have h286 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f497,c1f381]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k286
  have h285 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f501,c1f368]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k285
  have h284 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f497]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k284
  have h283 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f564,c1f284]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k283
  have h276 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f287]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k276
  have h275 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f286,c1f276]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k275
  have h274 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f306,c1f275]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k274
  have h273 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f287,c1f274]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k273
  have h272 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f273]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k272
  have h271 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f564,c1f272]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k271
  have h253 := RegChain.out_sound m.run m.bounds hin B (known:=[]) (by simp) c1k253
  have h252 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f253]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k252
  have h251 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f830,c1f252]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k251
  have h174 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f368,c1f285]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k174
  have h173 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f850,c1f174]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k173
  have h149 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f271]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> assumption) c1k149
  have h148 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f283,c1f149]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k148
  have h145 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f850,c1f148]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k145
  have h144 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f283,c1f145]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k144
  have h43 := RegChain.out_sound m.run m.bounds hin B (known:=[c1f564,c1f251]) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> assumption) c1k43
  intro t ht
  simp only [c1tops,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.InvLe_1_40
end
