module

public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange
public import ArtGallery.Orthogonal.BoundaryPoint.RegChain
public import ArtGallery.Orthogonal.BoundaryPoint.WingOrder.Ordinary_40_200_520
public import ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520.C2Defs

/-! Range data of profile `Ordinary_40_200_520`: `C2I1` (generated). -/
@[expose] public section
namespace ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520
open MarginCert RegisterTable RegisterOrder KronCert IndexedWing ShapeRefs RoomCoordinates CopyChannel CopyMatch CopyRange
open WingOrder.Ordinary_40_200_520
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def c2L2L : Ex := (.lit ([[[-69578949440000],[641280640000]],[],[[6406400]]] : P3))

noncomputable def c2L2X22N : Ex := c2N35
noncomputable def c2L2X22D : Ex := c2D35
noncomputable def c2L2X22C : Ex := (.lit ([[[-25025]]] : P3))

theorem c2L2X22cof : RegCert.auto (.sub (.mul c2L2X22D c2L2X22C) c2L2L)=true := by decide +kernel

noncomputable def c2L2X61N : Ex := c2N1214
noncomputable def c2L2X61D : Ex := c2D1214
noncomputable def c2L2X61C : Ex := (.lit ([[[-34789474720000],[320640320000]],[],[[3203200]]] : P3))

theorem c2L2X61cof : RegCert.auto (.sub (.mul c2L2X61D c2L2X61C) c2L2L)=true := by decide +kernel

noncomputable def c2L2X71N : Ex := (.lit ([[[29254225]],[],[[-2]]] : P3))
noncomputable def c2L2X71D : Ex := (.lit ([[[50050]]] : P3))
noncomputable def c2L2X71C : Ex := (.lit ([[[-1390188800],[12812800]],[],[[128]]] : P3))

theorem c2L2X71cof : RegCert.auto (.sub (.mul c2L2X71D c2L2X71C) c2L2L)=true := by decide +kernel

noncomputable def c2L2Y2N : Ex := (.lit ([[[-3]]] : P3))
noncomputable def c2L2Y2D : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2L2Y2C : Ex := (.lit ([[[-69578949440000],[641280640000]],[],[[6406400]]] : P3))

theorem c2L2Y2cof : RegCert.auto (.sub (.mul c2L2Y2D c2L2Y2C) c2L2L)=true := by decide +kernel

noncomputable def c2L2Y20N : Ex := c2N1199
noncomputable def c2L2Y20D : Ex := c2D1199
noncomputable def c2L2Y20C : Ex := (.lit ([[[-69578949440000],[641280640000]],[],[[6406400]]] : P3))

theorem c2L2Y20cof : RegCert.auto (.sub (.mul c2L2Y20D c2L2Y20C) c2L2L)=true := by decide +kernel

noncomputable def c2L2Y29N : Ex := c2N525
noncomputable def c2L2Y29D : Ex := c2D525
noncomputable def c2L2Y29C : Ex := (.lit ([[[-400400]]] : P3))

theorem c2L2Y29cof : RegCert.auto (.sub (.mul c2L2Y29D c2L2Y29C) c2L2L)=true := by decide +kernel

noncomputable def c2L2P : Ex := (.sp ⟨2,0,[(84,6,SP.join 8000 [0x7772a4d00200000a0000000b671f7844340010001030000026a9a6b3c740500000000180022d55d5a5c18f9a00040008040ec36e10cc0895cc50000000203907509879e68df45fa001000001])]⟩)

theorem c2L2ok : signed (1/65:ℚ) (2599/5005:ℚ) (67979/130130:ℚ) (detX (.mul c2L2X71N c2L2X71C) (.mul c2L2Y2N c2L2Y2C) (.mul c2L2X61N c2L2X61C) (.mul c2L2Y20N c2L2Y20C) (.mul c2L2X22N c2L2X22C) (.mul c2L2Y29N c2L2Y29C)) c2L2P (-1)=true := by decide +kernel

noncomputable def c2L2K : Ex := (.lit ([[[-1]]] : P3))

theorem c2L2Lne : RegCert.auto (.sub (.mul c2L2L c2L2K) (.mul c2L2X22D (.lit [[[25025]]])))=true := by decide +kernel




noncomputable def c2deepL : Ex := (.sp ⟨1,0,[(60,8,SP.join 8000 [0x190000000005800000004c5ec8000000280000098bd900000000212000308d41a600010000090000e94be9e6400000084005ce9450216200400002317056510b10000200020e091cf722fe80000000007]),(117,9,SP.join 8000 [0x1099989d08aa67100100010600000000001a36015b0e4242b9200000001800000000fffb70628221d44f000010001050000001b1e0ab7b0162fced1a000000000140000000bcc85ff9d2e806a000000100010400000240b1fb70220f5b7cf500000400040c0003d1adbc4419be0919d75a0000000000301e8d6de220cdf048cebad0000000400040b3cbc4495b9d215b6e78b4a0000000000002])]⟩)

noncomputable def c2deepY30N : Ex := c2N220
noncomputable def c2deepY30D : Ex := c2D220
noncomputable def c2deepY30C : Ex := (.lit ([[],[],[[1]]] : P3))

theorem c2deepY30cof : RegCert.auto (.sub (.mul c2deepY30D c2deepY30C) c2deepL)=true := by decide +kernel

noncomputable def c2deeponeN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2deeponeD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2deeponeC : Ex := (.sp ⟨1,0,[(60,8,SP.join 8000 [0x190000000005800000004c5ec8000000280000098bd900000000212000308d41a600010000090000e94be9e6400000084005ce9450216200400002317056510b10000200020e091cf722fe80000000007]),(117,9,SP.join 8000 [0x1099989d08aa67100100010600000000001a36015b0e4242b9200000001800000000fffb70628221d44f000010001050000001b1e0ab7b0162fced1a000000000140000000bcc85ff9d2e806a000000100010400000240b1fb70220f5b7cf500000400040c0003d1adbc4419be0919d75a0000000000301e8d6de220cdf048cebad0000000400040b3cbc4495b9d215b6e78b4a0000000000002])]⟩)

theorem c2deeponecof : RegCert.auto (.sub (.mul c2deeponeD c2deeponeC) c2deepL)=true := by decide +kernel

noncomputable def c2deepvDN : Ex := (.lit ([[[50050]]] : P3))
noncomputable def c2deepvDD : Ex := (.lit ([[],[],[[1]]] : P3))
noncomputable def c2deepvDC : Ex := (.sp ⟨1,0,[(60,8,SP.join 8000 [0x190000000004800000004c5ec8000000200000098bd90000000020e000308d41a600010000070000e94be9e6400000083005ce9450216200400001b17056510b10000200020a091cf722fe80000000005]),(117,9,SP.join 8000 [0x1099989d08aa67100100010400000000001a36015b0e4242b9200000001000000000fffb70628221d44f000010001030000001b1e0ab7b0162fced1a0000000000c0000000bcc85ff9d2e806a000000100010200000240b1fb70220f5b7cf50000040004040003d1adbc4419be0919d75a0000000000101e8d6de220cdf048cebad000000040004033cbc4495b9d215b6e78b4a0000000000000])]⟩)

theorem c2deepvDcof : RegCert.auto (.sub (.mul c2deepvDD c2deepvDC) c2deepL)=true := by decide +kernel

noncomputable def c2deepP : Ex := (.sp ⟨3,0,[(73,9,SP.join 8000 [0x9600000100001700000000112eed00004000058000001ca38b000000100011500004a7175263db88000000540000aef8ef6cb0000100011400b016d1c5a498f0000000050015df1ded96000000100021393d084234d5ec00000000044c6ae6c7077f67800001000212]),(111,12,SP.join 8000 [0x8b6c6ab818d66a7c500100001300000004e9b412dced61c71b000000011200000416e79ecb3d5229a3320001000012000000d0764a3cc500fdad21e000000211000013ec916a6066599a0046d001000111003800768b5ad98f3ae8a53dd801000011000137a5ee462ec9522b31dc000000021003edd892d23e8593f05335000001000110a4b8f0350502294f00ddafab00000000100000198345dfae744ad4b000000000030f7e92e6ee356cd13087a79f75400000020f011fe835c02f3ad2ffaef750000100030e]),(144,12,SP.join 8000 [0x59b0fe389d8df84f8325ef75cc700080008780000bd1b0fe296ee893e9c64bfd5d6c7800000003c000000dfb23a01f3c21f163f7da232f0000000041c0001e3d747ae3881e447e1f39a495a30000100010e00a058e0b7e9a083b98af4bab560b0d20000000007000000067687fbc0a17187a584ee180000004000c34005dd2fb7f132195a961a5207336dcec000200041a1309620ef1019df9f99734957a4c7083000000010da017c97d7f98ec1d8535613444f331200000000006800021fda8cbeb46205b6fddda7018b800004000c30e4e4ee26ab2b83278bc61fb3745e4bc0000200041800217486efe43e7f79d6779f1ff84000000000030b]),(185,16,SP.join 8000 [0x4616b13f3b0575ef7d7f267651cde9ac4a000000004300000003a3bf7585dd30d3d8956b8598cabb6ed2840000100000c000000046e26f4b128d9a18eb8dbe5fa10564518000000400082c0000105e1933f5faa044a3685d45fa63b6da80a000000000010b0000ee01e0f52faa0211e04aed0e26da5fc4e1a0000000400002c00000000891d369f3afb3c51a18e37927613cf9900000000030a000009591e9bd6080ac4fd14e4d8d74e7952e4440000004000828005c24d69efba29070f1fc00d3a72c8b2212710d40000000010a08134620505375f59d5bbcbfa99680d5e65977b37000004000028000003ca4efd4ced13cec32443d5882c448c31800000000003090001a52e93ce55707210781f9f10c02c1a77d3a00000004000824108981be1fb18add4d1bc9b7c39b8b211a9e3fe0000000000109dc4a57bbb8ccc543668619ca38208c98570323200000004000024002e25a8ce208bc97cd27e901b122b22afdc00000000000003083035a30ad5d197bfd9293f0715fa1449aebf00000000004000820041d089acfeed18965c50dfe0c07b580ffa2f400000000000307]),(216,13,SP.join 8000 [0xa859ff9589f751e7efdbee6b303865a5acaa3a00000000000001080000140a46e8bf5b049702b6604bf3370e7de1930bca40000000008000040000004275f1ecc3b76908c8709441dbc730add10bc05300000000400081c0009ecb751d4ac1852ddced54db43ad9aaaecfbb95df4a0000000000020e01ea9999193985a37c6864ef4f2ecc2386c7aab94f1cbe000000010000070000000e88b5aec458ad05dbc994d63a2271529755ee00000000000001830000041c451115b4acb4520696352a959c1d1935671f00000000004000818006ebc1e5112a7df450c28bc6263a0cc65d57dba3a1e000000000000020c0b76050f43a4b4096c75cc001b1cef3d4639b264526400000000010000060000b031cf702888d1b8017d734e878d85d8152ce4000000000000000182804d15cac111bbdbc080a6e2725b4dea8e8943a3c0000000000000000081662673fb57ddd261327e17c542128f09c7c33f98c6400000000000200020a44f27639147b5c2bae298f850c4ece4373fc81ef63900000000000000204]),(250,9,SP.join 8000 [0x2f2335a830535f5896dbacc45c57a510b1ad61d3d230000000000000000005000002211be431fedc5f504ca0ca1f6e666b3602feba6c66135e000000000000002080001d129481aa29ed43b60de360028159f9aeee0871f69aef557000000000040000100000001a4802c330a3901542ecc5bad49491ccee18f55b6510000000000000000101800002c8e14aee8754a440b756736bc63df2d6ba64ff4f1552000000000000100010300012e237c42185b5f9d6db423eb2d85416c01ffce350489410000000000000000006000591c295dd0ea948816eace6d78c7be5ad74c9fe9e2aa400000000000000000080809711be210c2dafceb6da11f596c2a0b600ffe71a8244a08000000000000008000814007051501a95d031c7f6c9c96657d1d236c7572bc361606400000000000000000002])]⟩)

theorem c2deepok : signed (1/65:ℚ) (2599/5005:ℚ) (67979/130130:ℚ) (linX (.mul c2deeponeN c2deeponeC) [(1,(.mul c2deepvDN c2deepvDC)),(-1,(.mul c2deepY30N c2deepY30C)),(1,(.mul c2deeponeN c2deeponeC))]) c2deepP (1)=true := by decide +kernel

noncomputable def c2deepK : Ex := (.lit ([[[1]]] : P3))

theorem c2deepLne : RegCert.auto (.sub (.mul c2deepL c2deepK) (.mul c2deepY30D c2deepvDD))=true := by decide +kernel




noncomputable def c2H43L : Ex := (.lit ([[[-173773600],[1601600]],[],[[16]]] : P3))

noncomputable def c2H43Y29N : Ex := c2N525
noncomputable def c2H43Y29D : Ex := c2D525
noncomputable def c2H43Y29C : Ex := (.lit ([[[-1]]] : P3))

theorem c2H43Y29cof : RegCert.auto (.sub (.mul c2H43Y29D c2H43Y29C) c2H43L)=true := by decide +kernel

noncomputable def c2H43oneN : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2H43oneD : Ex := (.lit ([[[1]]] : P3))
noncomputable def c2H43oneC : Ex := (.lit ([[[-173773600],[1601600]],[],[[16]]] : P3))

theorem c2H43onecof : RegCert.auto (.sub (.mul c2H43oneD c2H43oneC) c2H43L)=true := by decide +kernel

noncomputable def c2H43P : Ex := (.sp ⟨2,0,[(53,9,SP.join 8000 [0x801000004000000001d538000000c0000018704001000102000013e15010000000080000b32bf73800001010012fc0891cf04000004012a9e9c080010002001e5d70cdb0400000040229b6f9f215800000000])]⟩)

theorem c2H43ok : signed (1/65:ℚ) (2599/5005:ℚ) (67979/130130:ℚ) (linX (.mul c2H43oneN c2H43oneC) [(3,(.mul c2H43Y29N c2H43Y29C)),(-7,(.mul c2H43oneN c2H43oneC))]) c2H43P (1)=true := by decide +kernel

noncomputable def c2H43K : Ex := (.lit ([[[-1]]] : P3))

theorem c2H43Lne : RegCert.auto (.sub (.mul c2H43L c2H43K) c2H43Y29D)=true := by decide +kernel

end ArtGallery.Orthogonal.BoundaryPoint.CopyRange.Ordinary_40_200_520
end
