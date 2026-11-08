module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Lower_40_200_1000
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000.C2Defs

/-! Range data of profile `Lower_40_200_1000`: `C2I1` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Lower_40_200_1000
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def c2L2L : Ex := (.lit ([[[69578949440000],[-641280640000]],[],[[19219200]]] : P3))

noncomputable def c2L2X22N : Ex := c2N35
noncomputable def c2L2X22D : Ex := c2D35
noncomputable def c2L2X22C : Ex := (.lit ([[[25025]]] : P3))

theorem c2L2X22cof : RegCert.auto (.sub (.mul c2L2X22D c2L2X22C) c2L2L)=true := by decide +kernel

noncomputable def c2L2X61N : Ex := c2N1212
noncomputable def c2L2X61D : Ex := c2D1212
noncomputable def c2L2X61C : Ex := (.lit ([[[34789474720000],[-320640320000]],[],[[9609600]]] : P3))

theorem c2L2X61cof : RegCert.auto (.sub (.mul c2L2X61D c2L2X61C) c2L2L)=true := by decide +kernel

noncomputable def c2L2X71N : Ex := (.lit ([[[29254225]],[],[[6]]] : P3))
noncomputable def c2L2X71D : Ex := (.lit ([[[50050]]] : P3))
noncomputable def c2L2X71C : Ex := (.lit ([[[1390188800],[-12812800]],[],[[384]]] : P3))

theorem c2L2X71cof : RegCert.auto (.sub (.mul c2L2X71D c2L2X71C) c2L2L)=true := by decide +kernel

noncomputable def c2L2Y2N : Ex := (.lit ([[[-3]]] : P3))
noncomputable def c2L2Y2D : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2L2Y2C : Ex := (.lit ([[[69578949440000],[-641280640000]],[],[[19219200]]] : P3))

theorem c2L2Y2cof : RegCert.auto (.sub (.mul c2L2Y2D c2L2Y2C) c2L2L)=true := by decide +kernel

noncomputable def c2L2Y20N : Ex := c2N1197
noncomputable def c2L2Y20D : Ex := c2D1197
noncomputable def c2L2Y20C : Ex := (.lit ([[[69578949440000],[-641280640000]],[],[[19219200]]] : P3))

theorem c2L2Y20cof : RegCert.auto (.sub (.mul c2L2Y20D c2L2Y20C) c2L2L)=true := by decide +kernel

noncomputable def c2L2Y29N : Ex := c2N525
noncomputable def c2L2Y29D : Ex := c2D525
noncomputable def c2L2Y29C : Ex := (.lit ([[[400400]]] : P3))

theorem c2L2Y29cof : RegCert.auto (.sub (.mul c2L2Y29D c2L2Y29C) c2L2L)=true := by decide +kernel

noncomputable def c2L2P : Ex := (.sp ⟨2,0,[(84,6,SP.join 8000 [0x43307cb500200000a00000022355e68cc9c0000001030000073fcf41b55c0f00080000180022d55d5a5c18f9a00040008040ec36e10cc0895cc50000000203907509879e68df45fa001000001])]⟩)

theorem c2L2ok : signed (1/65:ℚ) (4999/5005:ℚ) (130379/130130:ℚ) (detX (.mul c2L2X71N c2L2X71C) (.mul c2L2Y2N c2L2Y2C) (.mul c2L2X61N c2L2X61C) (.mul c2L2Y20N c2L2Y20C) (.mul c2L2X22N c2L2X22C) (.mul c2L2Y29N c2L2Y29C)) c2L2P (-1)=true := by decide +kernel

noncomputable def c2L2K : Ex := (.lit ([[[1]]] : P3))

theorem c2L2Lne : RegCert.auto (.sub (.mul c2L2L c2L2K) (.mul c2L2X22D (.lit [[[25025]]])))=true := by decide +kernel




noncomputable def c2deepL : Ex := (.sp ⟨1,0,[(70,9,SP.join 8000 [0x546000000000b000000000157aa84000000140000000abd54200004000424000016c236c5d0000000004800000577c77b658010001080000e4dcf9e32130000000100379e611b2c720000400041fedee5e58d686c0000000003a762027484ea671001000106]),(117,9,SP.join 8000 [0x1dba28ccc0c010ae480000000600000000400cc77a8ad7b68dc000040004140000006ca75cf6becd793cee800000000050000001a8c2d7f21a8a0ee8000000400041000003c023182096a811b1c000000000000400000240b1fb70220f5b7cf500000400040c0003d1adbc4419be0919d75a0000000000301e8d6de220cdf048cebad0000000400040b3cbc4495b9d215b6e78b4a0000000000002])]⟩)

noncomputable def c2deepY30N : Ex := c2N220
noncomputable def c2deepY30D : Ex := c2D220
noncomputable def c2deepY30C : Ex := (.lit ([[],[],[[1]]] : P3))

theorem c2deepY30cof : RegCert.auto (.sub (.mul c2deepY30D c2deepY30C) c2deepL)=true := by decide +kernel

noncomputable def c2deeponeN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2deeponeD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2deeponeC : Ex := (.sp ⟨1,0,[(70,9,SP.join 8000 [0x546000000000b000000000157aa84000000140000000abd54200004000424000016c236c5d0000000004800000577c77b658010001080000e4dcf9e32130000000100379e611b2c720000400041fedee5e58d686c0000000003a762027484ea671001000106]),(117,9,SP.join 8000 [0x1dba28ccc0c010ae480000000600000000400cc77a8ad7b68dc000040004140000006ca75cf6becd793cee800000000050000001a8c2d7f21a8a0ee8000000400041000003c023182096a811b1c000000000000400000240b1fb70220f5b7cf500000400040c0003d1adbc4419be0919d75a0000000000301e8d6de220cdf048cebad0000000400040b3cbc4495b9d215b6e78b4a0000000000002])]⟩)

theorem c2deeponecof : RegCert.auto (.sub (.mul c2deeponeD c2deeponeC) c2deepL)=true := by decide +kernel

noncomputable def c2deepvDN : Ex := (.lit ([[[50050]]] : P3))
noncomputable def c2deepvDD : Ex := (.lit ([[],[],[[1]]] : P3))
noncomputable def c2deepvDC : Ex := (.sp ⟨1,0,[(70,9,SP.join 8000 [0x5460000000009000000000157aa84000000100000000abd5420000400041c000016c236c5d0000000003800000577c77b658010001060000e4dcf9e321300000000c0379e611b2c7200004000417edee5e58d686c0000000002a762027484ea671001000104]),(117,9,SP.join 8000 [0x1dba28ccc0c010ae480000000400000000400cc77a8ad7b68dc0000400040c0000006ca75cf6becd793cee800000000030000001a8c2d7f21a8a0ee8000000400040800003c023182096a811b1c000000000000200000240b1fb70220f5b7cf50000040004040003d1adbc4419be0919d75a0000000000101e8d6de220cdf048cebad000000040004033cbc4495b9d215b6e78b4a0000000000000])]⟩)

theorem c2deepvDcof : RegCert.auto (.sub (.mul c2deepvDD c2deepvDC) c2deepL)=true := by decide +kernel

noncomputable def c2deepP : Ex := (.sp ⟨3,0,[(80,9,SP.join 8000 [0x1ab26000001000017000000000adfb1fa000080000b0000006cbcf3c400000000004540003bb3213fc41b10c0200002a00002137a8a73bd0000000011402571fb3b2e5ef9ba00080000a001bae61e0b1d8000000400084f06163e7f3689020ac0000002260b4656fdca6fea800001000212]),(124,15,SP.join 8000 [0x37190c260631fd125e8c00400004c000000005a2b323fa52a96de97e00000002240000003ee83978f17ac33434a660001000012000000024a34f2beb91114c88e790008001088000021e7c0a5a7f28ebd04167c7c0000004440006bc309a636545b505314073970020000220000037e3dba2e83a9a5fec8aa40001000210000e26ec3d33e62ace20944666000000000880538dc847abae604393ace80b0640004000040000000561b0bd2ecc87c8dd2000000000061e011b0019bf9b03d56e85b0a5e5fc00100020fbbbcef6f1434f28dcd23495795650000000878000ea92a1c48a31811914e538c00000000c3b18788d54e757046efcbf658ddd0000200041c180bc810db33bace89ad516a000000000030d]),(156,12,SP.join 8000 [0x3bae2732271fb63d20dea7473302f5000800007800001a63adaa7d51720627adba7ccc2350000000004380006d337776355c76fe743ea725ef378d18000200001c00001d916cf0c1510423a39006021a98e76000100020d00107057aa62febaafcec66e8e5bd90004180000000868258cd2eb3c195e1849322a5bc555a6db70000040000340000035afd5c5e69d969b9110dd100251400000000618003cc4728d88575feee19a5adb69ca4f360000100020c569b0cc2937be5959c473810ed65a09cf84000000008600011955d77e926668508ff01d0bc1ff00000000000c2e5474d0e9fbfd2f9d3cc4ed3e5febe26c00000020004163ecb25eb6d48bdb9be90b9179a15bcf9900000000030a]),(191,16,SP.join 8000 [0x46a7deecf03ae4aaba46fbca389f04e4aa940000100000c00000015f69c950842c8b19cf4289f5106c7d6ae4000000000010b000006e0a1d742c4ff8e168333359a36e40d73e00000000100000b000000379e8698f82c51f6fc3111579f4dd212111000000100020a00006f7a2d99847a45381f95885a38ec9dec58310d40000000010a0025edd5e7a79249497779943fdd0731c336f69ecdc0000100000a000000049ac737c409172d48d1f695c67ac5fd9780000000000309000018c4257fa439564392dc44b5c7ef778af43c800000010002090088cdf7ae4acae5866d1ccb0829edd893d94265600000000001093df1db7a14c6721c838cfdedbb3f847f02749cf080000001000009000030302f8842971f8a784e29085185ff405a000000000000030800c21d08d28b29eb288e66f249a1e79b1c92220000000001000208baf742b6200947868ec28ddbf31069810216bb8000000000000108001da13d3d3066e751a1046a3b119b98ef2fa2f400000000000307ec36e4f9233298ea5def3abb921d74b8111f014c000000010002071d116b5d88b15a0bb79329ac7444e2a52eabdc0000000000000306]),(221,12,SP.join 8000 [0xcec4da724d5110acf5f614e96cd2f1ac6d80afee000000000400002000004cd21a5b8c47f62f11d753f9df0fb2f51c07874efa50000000000010700078785a031f69694578006da1ee2cda9689d864fe872f80000000400001c00000087b864993a1c333c03bda05b26a4324435d0bc40000000000000206000700eeff2d8d991ade75378419661195c3e21c90bebc00000000000004180e30ebd578e6d3968b7ec531cafa3812a21875b8d40440000000001000006000005818e7b8144468dc00beb9a743c6c2ec0a96720000000000000000c1400138258411afa065f8a3ac09412b477a51064069c000000000000000020504d6035cacefafa8a147e838eaed8eb34b1279555cc8000000000004000417046e9df326f3afc6b928449c696a82a0c8f5089bb0000000000000000000509ae3879de4c9bae2acb465f69cfa4421ad8a329bd8e40000000000000081349005866147202a85d98b75a9292399dc31eab6ca20000000000000000203]),(250,7,SP.join 8000 [0x3b05dace2efcaecb63dd5d189bd4b49be950619e46426bc0000000000000041000035824a29ea25b4de6f6d703f9652528a9a7b340961f45eaae0000000000800002000002c8e14aee8754a440b756736bc63df2d6ba64ff4f1552000000000000100010300012e237c42185b5f9d6db423eb2d85416c01ffce350489410000000000000000006000591c295dd0ea948816eace6d78c7be5ad74c9fe9e2aa400000000000000000080809711be210c2dafceb6da11f596c2a0b600ffe71a8244a08000000000000008000814007051501a95d031c7f6c9c96657d1d236c7572bc361606400000000000000000002])]⟩)

theorem c2deepok : signed (1/65:ℚ) (4999/5005:ℚ) (130379/130130:ℚ) (linX (.mul c2deeponeN c2deeponeC) [(1,(.mul c2deepvDN c2deepvDC)),(-1,(.mul c2deepY30N c2deepY30C)),(1,(.mul c2deeponeN c2deeponeC))]) c2deepP (1)=true := by decide +kernel

noncomputable def c2deepK : Ex := (.lit ([[[1]]] : P3))

theorem c2deepLne : RegCert.auto (.sub (.mul c2deepL c2deepK) (.mul c2deepY30D c2deepvDD))=true := by decide +kernel




noncomputable def c2H43L : Ex := (.lit ([[[173773600],[-1601600]],[],[[48]]] : P3))

noncomputable def c2H43Y29N : Ex := c2N525
noncomputable def c2H43Y29D : Ex := c2D525
noncomputable def c2H43Y29C : Ex := (.lit ([[[1]]] : P3))

theorem c2H43Y29cof : RegCert.auto (.sub (.mul c2H43Y29D c2H43Y29C) c2H43L)=true := by decide +kernel

noncomputable def c2H43oneN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2H43oneD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2H43oneC : Ex := (.lit ([[[173773600],[-1601600]],[],[[48]]] : P3))

theorem c2H43onecof : RegCert.auto (.sub (.mul c2H43oneD c2H43oneC) c2H43L)=true := by decide +kernel

noncomputable def c2H43P : Ex := (.sp ⟨2,0,[(53,9,SP.join 8000 [0x48010000040000000057fa8400000c000004950c00000010200003ba3f030040000080000b32bf73800001010012fc0891cf04000004012a9e9c080010002001e5d70cdb0400000040229b6f9f215800000000])]⟩)

theorem c2H43ok : signed (1/65:ℚ) (4999/5005:ℚ) (130379/130130:ℚ) (linX (.mul c2H43oneN c2H43oneC) [(3,(.mul c2H43Y29N c2H43Y29C)),(-7,(.mul c2H43oneN c2H43oneC))]) c2H43P (1)=true := by decide +kernel

noncomputable def c2H43K : Ex := (.lit ([[[1]]] : P3))

theorem c2H43Lne : RegCert.auto (.sub (.mul c2H43L c2H43K) c2H43Y29D)=true := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Lower_40_200_1000
end
