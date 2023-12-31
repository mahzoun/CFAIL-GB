## Source: https://extgit.iaik.tugraz.at/krypto/hadeshash/-/raw/master/code/poseidonperm_x3_64_24_optimized.sage

class Poseidon:
    def __init__(self, prime=2^64-2^8-1, R_F=8, R_P=42, t=24):
        F = GF(prime)
        self.t, self.n, self.R_F, self.R_P, self.prime, self.F = t, n, R_F, R_P, prime, F

        round_constants = ['0x240ec2a793108b4a', '0x753452ad8cbbbecb', '0xa3612a53da19a265', '0x18a083f17b5a94eb', '0x30d1c3ecb4f44b99', '0xaea865a3e5830f71',
                           '0x4a9134c89190acc6', '0xed37c99a612065b1', '0xafd9964e15975e77', '0xa77147766c1ff75e', '0x1f075012654c408f', '0xc5e11b29262d9283',
                           '0x6b6495600eb3ac52', '0x2b3b599ae4fa1d12', '0x90cda513782b872f', '0x78d9b4ea0f82d0e9', '0xbcbe92c86e626013', '0xa24fb10ca2a94fe8',
                           '0xca3d8d1ebcc8b0b8', '0x01f19977b5ae425b', '0xdcb91f4a2ee555e1', '0x522fc03d8de5625b', '0x8093493f225f5fe0', '0xe34925160dd8ac6a',
                           '0x0d849db4c9677f3e', '0xdb3c9dba3951d80a', '0x69ebf310531af9cb', '0x618c6e79c2131c9a', '0xf753bfda5bea2713', '0xc764d2dcfe66b834',
                           '0x1428f86c920dc41f', '0x32eec3f568ba6a6a', '0xd348b99d1be142d1', '0x5a54339e5cf85764', '0xfcfcfcd93a85db2c', '0x5bf91d3330de1254',
                           '0x7497efbc720c4d29', '0xb7f823baf4fb4ad3', '0xecbdc0ce5ce155f7', '0x1e98e24a11060158', '0xd68cc1bc7a734e3b', '0x8b5192beefe56d76',
                           '0xcb37590292ed5d94', '0x3c0f4ac4442e718d', '0x7f28481f271ac458', '0x95a29062b8b7ef10', '0x5e35d63f60ebe7a4', '0x6f0cce8765194a54',
                           '0xb2c5368f33cfdb88', '0x23d4c5242d9031d8', '0xa01e66ab5e6bf11d', '0x37b3c3f35a2c2db7', '0x6b0f16e664da3bc7', '0xa2edd28b4157761c',
                           '0x772f8d3d4b7bbe30', '0x067d7f034ea64273', '0x9c04b9ef0ad21b49', '0xec615fcfe5fb17e3', '0xe5d5a133b594b39d', '0x5575c2ad9cfb2e71',
                           '0x8b8bec6fa05ae8ec', '0xfdfe46961b74f8ca', '0x81826d165c8db1f4', '0xebb8dd7f53d2873a', '0xa74d8725a61f697c', '0xa48bbebeb12e5ba1',
                           '0x1dc2cfba8304fb0d', '0x121ce1466d109dd6', '0x2e4a7c3aba839378', '0x540a4d98e030dcdc', '0x215ac5039c8dacf7', '0x8627aac1074f6776',
                           '0xbd9f007a00342dad', '0x0485d9997c5d2d43', '0xf73dc1f105ba7b82', '0x75dfe4727676a769', '0x9226a74d24479a98', '0x1f9526e943307c60',
                           '0xf8ec7859af0ac374', '0xbf084ca320167a51', '0x19225ef89b83a433', '0x4eea3af3cf87a21d', '0x5f32bfe642a25785', '0xee18341408e7109e',
                           '0x095086a0fd9e22f4', '0x24bbb72c5af99867', '0xf0bdd8ee27e7a897', '0x19c9f25475ec0a13', '0x9fae6ed0f262b68c', '0x8521b8743284e615',
                           '0x11341ea6613ab6ed', '0x66efe6ca18cd3dca', '0xf1ac5951a2934237', '0x22f7e35282498908', '0xb5bcdc16593c6674', '0x865eaa9fa7c40873',
                           '0x9dee60da82ac4465', '0x22735f881786cc39', '0x6de9f9171436b66e', '0xf2aadeaa6a66b7ad', '0x4aacc905f9272cb4', '0x2c2714c649e42a81',
                           '0x76d73405217d9dc7', '0xc883b51c111a8c32', '0x75dc8b2a293b801a', '0xcca8a5875b768909', '0xb9fd56aef43fe7cc', '0xafbfec0102d26c2c',
                           '0x5157f8d356757a65', '0x26e3b538e13b9d5c', '0xca1497b238a3dc52', '0x995c0df77c5b3940', '0x7ff238ddc7075582', '0xa6efe8632d790673',
                           '0x3f402fcafb803b75', '0xd0a9b5989fa80648', '0xd731da881957d177', '0xce282dcdbed66f47', '0x1270fea846832c28', '0x873da44928addef1',
                           '0x3946531d53229dec', '0x5f09a6e3919f98c7', '0x8ea315a8fc0618f9', '0x4fd30e28e515e81c', '0x2cdbf5e36d8c63a5', '0xcce53304047e771a',
                           '0xb710cb8e0564ca50', '0x1631a30bdc219de3', '0xde3e13bfac4ab80c', '0xc37e18414100ead5', '0x99e5043b30387161', '0x3c6bb225d1d78d15',
                           '0x65c5d73b4a5f9807', '0x137c582109bc3643', '0x05f762e5b1d480fd', '0xb389c617c45d5bd0', '0x2a23ba94c54ad1ef', '0xeb4440f0a237d56a',
                           '0x9d503447cce854b3', '0xfc5b688737c2aae9', '0x80f39542543f321c', '0xbaf3e8826b9e7c31', '0x1f7e8de645be342f', '0xd5c2dcab1d053e13',
                           '0x986a4a8db3280f18', '0x4b242191c7dadd25', '0x50882bd23adf7857', '0x09f16b633e545bdc', '0x5e0981215a746ce5', '0x9ece3a04ded2e454',
                           '0x8a7d4f600e85d88b', '0xab49152709ed581d', '0xed825bf8b3d32ab2', '0x1f37d6e31dd92ee7', '0x4a766830058f5e67', '0xd413d3bb4acf6432',
                           '0x93da3397b6581f7a', '0x5fd4de23b579e4f8', '0xcf0bb8b34bfed3e6', '0x1a31a6eccc154f82', '0x4ec5a45b2444daea', '0x5cb0b6b9fe239e7e',
                           '0x35a035640d1457f8', '0x6dbc1e53fa738977', '0x5efa24c87a749e3a', '0x27613437239afc6b', '0xfca89d793bf3a0c1', '0x993a7c1d8b509373',
                           '0xae990f255bf5e977', '0x7b7acad0dea808d9', '0xe4df51bda3d6834a', '0x3e7516a279ce8e04', '0xc50749a33a60fb83', '0x8eb497c64e56d7a9',
                           '0xade425408c5d2fe5', '0xb6f34f730c10daa1', '0xbcef2e56ac305d87', '0x2d2a447c10e46c62', '0x1580f32c34717e21', '0x84053458cf464329',
                           '0xd8fa9ab59dde6961', '0x82980512e0d69940', '0x4cde6a69a159dce9', '0xa504dce40d2b5a48', '0x110ca7f7d0cda6e2', '0xfa09f77131f1452e',
                           '0xb3226a341171e6d4', '0xdf3271ee4ddcd610', '0x10245cd637f7d033', '0x9e9b54ded7e50b22', '0x55f509f254b7e35e', '0x770305e05b566059',
                           '0xc25639019180ef24', '0x34f10edac360c5f9', '0xa916820e3a4c0aa4', '0x771e31cdca908142', '0xc7483c5e864b3503', '0xa3c46f88d2848a1f',
                           '0x8038982788e3a966', '0x260490d7c9225b8b', '0x8f29b9bc9c9ff52b', '0x9eca64a99a2f4512', '0x173ae30db15d3cf4', '0x9dc0ad665c6f198e',
                           '0x08809d47fe8b8830', '0x062ae1e794799105', '0x87d4e118f187c9df', '0x909427dfb26e7106', '0xdd6ae0ed2b860e28', '0xb29665bd1eb2afa6',
                           '0x2c63db6fd4ee02dc', '0x35c5a2ffd39bc2ce', '0x875f62e7c53fc417', '0xe19d89ac6f2bc4fb', '0x0d14634389245057', '0x6be7c3348405623a',
                           '0x68a0148f85f02014', '0x053b66589a569cb6', '0x953b226a62f08b4c', '0x09d4508bb4810fc0', '0x95518a3826b0eec2', '0xb75ab99956105ca8',
                           '0xc82371d676d48c9a', '0x61b15247a05e9c21', '0x33af269eff1f825d', '0xd629b9b9047ab8ea', '0xc93068d389e2d4ea', '0xac10466f4b976c59',
                           '0x31d1ce7704841862', '0x0a484569fa243d73', '0xd7a6b9d534870cdc', '0x11750c56d10c784f', '0xc094fa6698940e8d', '0x8ddd68efe3868d4c',
                           '0x7c0096350bc9bfb6', '0xf425dd1b76edfbd3', '0xb6ab8ce0383e8a33', '0x622e65b931dbac28', '0x0b5568d0bf077fe9', '0xd6e3591de846152b',
                           '0xf239f23fd08164f9', '0x4863be619ee92e84', '0x24e8d490749e33e9', '0xa9000176c5e951c1', '0xe088ea688b9eb620', '0x0a7427f52cbf104a',
                           '0xcd0e6c197f77b6b1', '0x94be36b10c7d4930', '0xf74e110bc09d2f2f', '0x8441201952f59356', '0x109867dbccc9dd66', '0x5f164f533a6359e7',
                           '0xe572a712fc2b0ed3', '0x757d2ee09f334594', '0xad328750d711a41d', '0x5f24ae2d9e2b69f9', '0xb497f3cd4100261f', '0xb308050e303f7083',
                           '0x2b862ca16302f6ae', '0x95b657d9d9f5021b', '0x2e7d16c5bbaaef02', '0x70a4d93ec31ae87f', '0x88554a56246d7163', '0x9e5b0ac6ce73c344',
                           '0x87607583c1f22021', '0xeb490685514ade4e', '0x80ff79b55c59e727', '0xebaab6d2fe22b19f', '0xc2e80030efcee83e', '0xf75b0bb78bb6fcfb',
                           '0xd1febaed89c8cb71', '0xf9992ff4f4c50249', '0x256fa25efeee82d5', '0x0c59050402658413', '0xbead2aec63e55865', '0xfc4be776b30fe386',
                           '0x9494dddf06460fb5', '0xac11debba14ab0ca', '0xe3943487764df091', '0x5084dbd61e210259', '0x47b0cfcd64112240', '0x3f8b1ad5c852a1ab',
                           '0x918dbd53ea331324', '0x7a3ee799ce4a33b8', '0x91e359bcb7886b42', '0x184ea8a19fa8ae99', '0x25d77e20eddd6354', '0x348d82eacc7718e2',
                           '0x6602f76a41d1efe1', '0xdaf23c2e098b09bd', '0xd7b8be850e0e57a1', '0xc51e7df4f8855070', '0xb1bd2ff2feeb1804', '0x840b56248453fd57',
                           '0xf3ceed3a8b5099a3', '0x8fdedc805119ddbf', '0x79ce965dfd546956', '0x7ffc046b04f5959a', '0x8385d3fed9b19240', '0x9f400d4ee91cf32b',
                           '0xc1626c4b5968cc63', '0x594d31369bdf5d9a', '0x7b005ffaf67c2a4b', '0x592f256ff08a2eb4', '0xb55605f825a8bf54', '0x1a2e6ad796384de0',
                           '0x892c2daaf915145e', '0x972487031937f2ac', '0xf899e0e4bfc61c05', '0xd412469ff6514f25', '0x93157c74b40e7b75', '0x8f95241bbb036960',
                           '0x774bbff0a2135e8b', '0xbece3caa5fca59e2', '0xa70f7a3af5a9af91', '0x2053124fc4c73004', '0xb0903b76b359c884', '0x0a0091105a5b5bf1',
                           '0x9a9f5c0ca297c144', '0xe300fb7474171a63', '0x6abcf1d301c6552c', '0x6975ffd56f93dedd', '0x31be996a361e8ce4', '0x469a5228c8ac765a',
                           '0x907c31250ecc3ecc', '0x2021c7cd003ce15b', '0x1a2e2d1f753025b0', '0x4341fba21850eba1', '0x06ee53f346a972fb', '0x9c9fb9f30f5c983a',
                           '0x865d837be8597cc1', '0x4fb0998a2c433786', '0x95c3f50201471ad8', '0xa2a730f4f6e815f7', '0xad5c75c0774d82a8', '0x05dfdad6814c0599',
                           '0x5f1162f7dc6cd441', '0x3ec558a534156b7c', '0x00acc4391da75e5c', '0xd12933dfbb3ea285', '0xb521625654a8a6fa', '0x221da50d9cddf162',
                           '0xaa3549f789c9ec03', '0x44c4834b23cf5e75', '0x40d60d6766edb0ee', '0xd021a7d957ba9d47', '0xe0f75a57c3f5372a', '0x27b7495ad99cb77b',
                           '0xf0c0945d125d1dd6', '0x607465043244b65f', '0x878ff223416a7ecc', '0xe80317ceaa25121a', '0x63f6f68286976720', '0x415e604f07cd1961',
                           '0x53d80907802c1448', '0xfd3470ac4a2afb79', '0x2fec40d8e0a914ba', '0xafb4d0b5fddbea45', '0xa174d4056ef97d30', '0x2cbc5c415f9e0bbc',
                           '0x81ef52c672737433', '0x37b315d8abe01173', '0x81641522ec336fa2', '0xd1dcb4006f75db80', '0xe01057583981c09d', '0xe15c2fdbd2fa0868',
                           '0x1b7b78b61a3adab3', '0xd8e6a93d4858d348', '0x8a9e5a25ed078c23', '0xbc503d55df63fe72', '0xa248824148455705', '0x810b1b6390aa9aea',
                           '0xfeb4c64541d2c29b', '0x346c14905f941eb8', '0xd1fb93e8f22b778f', '0xe82c8622350aafc1', '0xee6db701e484e24e', '0x13701c397195d477',
                           '0xcf00aef6b66f3d86', '0x99620f5303aa7218', '0x387d20fbeee11457', '0x5dfdba7cf8c9a1f2', '0xdf2ac0bd2470f86c', '0xdfcc435769de8316',
                           '0x94c961a6d5467e9d', '0x8e8792275ff2233b', '0x0dd14a0dc251e970', '0x575289c45dfc9e0a', '0x042ab718496919ee', '0xc206f9ac07c65176',
                           '0xebb7fad74d70cc85', '0xd57ebb65db572846', '0xdd09c80720ceed7d', '0x873c363f00095267', '0x2e383339276e4093', '0x4f0d0782b2c8b737',
                           '0x8f878fc66a5a7850', '0xe843f529068ac009', '0xcda19e17f3b54390', '0x855fbf51c0d6c44a', '0x212b33c109a9e69c', '0x7a8e8eed51fab217',
                           '0x60ac3668f0153a22', '0x988f514a0249e121', '0x224ec281d7c0658e', '0xb644df07c7e8553c', '0xf5f41c3b9b9e2877', '0x3ebacfb67a9a3d27',
                           '0x65146220a3a8c0a9', '0x590cbc85158d1978', '0xd7f05c8122ec1932', '0xc3b6a635b5cc96fe', '0x6c27c5d509479abf', '0x213cd7dabcd6e78d',
                           '0x838394a5431c2262', '0xd5126b30e589b46b', '0xbeee79d6fd4f84df', '0xb5c0145be96a54e5', '0x9978b1c70566a3f4', '0x32aa9454c633afec',
                           '0xaff40f199d069bed', '0x4ff14e9914976425', '0x8a65f1d1eb6a251e', '0xefe6eac0a5eda30d', '0xffc68f979de172e4', '0xbcb3db712bcc55c6',
                           '0x93acf1aa6e8a9d22', '0xbbe2e847cf55cf43', '0x69ab97e431cee092', '0x881245ef49e2630e', '0xcd7dd1ce9d922e0c', '0x45c5d132ef40296d',
                           '0x343f80118aefd015', '0x43465c962ccdfc2b', '0x82721cb7b420ca20', '0x78e7e78fb9546ff6', '0xfd29b50d0f75dd85', '0x45d0c2853e73e828',
                           '0x1927823b3659c972', '0x36973da7f6c94489', '0x6b6b7abda0c9022f', '0x246554ee3f49b7f5', '0xdb2e964cd295f4a9', '0x60176cb18febc37a',
                           '0xab3ee9f462bb182f', '0x85a63e3a23c517cd', '0xf3eafd818e849912', '0xa71a472887e42560', '0xa8497584dacae693', '0x5a767c9b5af33d10',
                           '0xbc7c55b85a3ec210', '0xe05d645b6ae931f2', '0xc12786849459e0f6', '0x40ba491713c91141', '0xd00653990ca2882c', '0x011bcce2af8947b3',
                           '0x7e02974d92a00607', '0xb83b5cb0bcdccf43', '0x564bab91568042d0', '0x1c63e60462c4e019', '0x5554fc74434296c4', '0xc5203ce4d2739ea0',
                           '0x4ac41c9434f93808', '0x605ecbf7258c092a', '0x2f3a78ef34ad4ae9', '0x044889efdd9aa67f', '0xb5e2e07a2f599281', '0xe09b7e66b2c03bf3',
                           '0xe03e874ed19e14a6', '0xda7ebb461927ebcb', '0x804471a032f8915f', '0x1396b9bb6811a42c', '0xdd71d36258b06442', '0x130df22639f33fac',
                           '0xf61739314787dee8', '0x1887569c23e6e352', '0x014ba79f34e6fce3', '0x8045bf85289d78cc', '0x12e4ebbbe7d1cad1', '0x375005b5be5091a7',
                           '0xc2a39a6a726ba40c', '0xf05f642162cae0f3', '0x7bf8d2344d8714c0', '0xa1b07d2740c5faae', '0x50ce5b0d7dfbe741', '0x0be409c08d9ffb8c',
                           '0xdae3b133e3c164f0', '0x93f7463331946134', '0x71e4d4584114328a', '0xf145cbdd12d6d7ab', '0x50edee2f406941b9', '0xd3972131bd7eada0',
                           '0x24fa8cd71b4eae21', '0xb52034e8b78ceccd', '0x5249785d00660bcf', '0x8ef3991c1d400dee', '0x5157a39b1bc5fa46', '0xc5ccf2b41253d1a6',
                           '0xb78b560cbb846e87', '0x4b4858ceff78d344', '0xd83782e72665a5fb', '0x67a9b40fdec2b07b', '0xd2fdbef12ded02a8', '0x377e3ced59300b66',
                           '0x6f8626cd1f73b995', '0xdbdc5ac70c2f1db5', '0xf8474fb2755d4e52', '0xc791b175eb895c14', '0x1ce7e03901233257', '0x07e72c154695f91a',
                           '0x9695730685df4b7a', '0x25f649edc3d06122', '0xbbc643aedc69500e', '0x0ac606eca1196a1b', '0xacb6ad902f55b53d', '0xa13dc1c7adf23c50',
                           '0xb2b2a9f836838c1d', '0xae3a777f83e462c1', '0x15275af835c10949', '0xf0616aa86758e9bb', '0xa64e610900966808', '0xb72da03bfcc05953',
                           '0xc91ec7c060da1d68', '0xcc58e551844cdad2', '0xafc7268b6bd92069', '0x859f91cb011a2187', '0xeef1076c8c7109a6', '0xbd2795d1630214c8',
                           '0xf366d8583f32ea90', '0xf26c94a7546605d7', '0x0cd09180d78fa6b3', '0x4b7868ba6da62733', '0x62d296ec2054b6ee', '0x3dd83963b81ec606',
                           '0x3d2dea21bf186e22', '0x0759723dc6d59f04', '0x36f4b39344cdc1f5', '0xf1d951516ea80e3b', '0xaee081f9d2fa1142', '0xa95fa79a5453e3e6',
                           '0xd13c71f5c90d60c0', '0xe1ea6eb5dbbd2563', '0xf6839746449acd72', '0xd92905f95cfe48e6', '0x209b2f366ecd2d4d', '0xce2e7a3e32324698',
                           '0x307af7f7ff6ef841', '0x12c470229ba56c9d', '0x42a7437137c34811', '0x7209d7d7c6d65434', '0xbca149c078e914ce', '0xffc49dfcd00ed664',
                           '0x24f7cf8fe7e0ebaa', '0xa2836a607ecf9828', '0x71a10299f72567e9', '0xb47f36509cf355b5', '0xc83fc41d0d1387e7', '0xb2a2e236f27469f9',
                           '0xadbb4aba85a35fbc', '0x5199ef01f475e0df', '0x9030bf2f679c8866', '0xd7ce53a695f7c660', '0x6c56c712bfdea91f', '0xb9964f64638eb87a',
                           '0x96790e4df82e0dac', '0x87ff84ee04028999', '0xc5bd94c7598bd77b', '0x7d82e4f8ada3e307', '0xc8c25a74c4c80ddb', '0x44b2ba2d02469440',
                           '0xe429cf826b538f50', '0x364022b037f9bd59', '0x19bfca9a2421a5f2', '0x3a1e127d18a6b2d8', '0xa72c048d26b5c02a', '0x9ef51363798d048e',
                           '0x650e70ba374f8db5', '0x6aa7c0b89fa7d5f3', '0x88b59973686e621e', '0x53479cfe59a786bf', '0x393e059636a6735a', '0x31199a2b2e9e05ec',
                           '0xa4f1abfa5aea6c88', '0x6e57a3d21676bce0', '0x648390659ac120f1', '0xffe5d8bd45073a28', '0xe2aec08796d412eb', '0xd347bcb985bd6c98',
                           '0xce0be57d467fd41b', '0xa8c83853d9af14f2', '0xf2211480b0cac644', '0x938f699af2dccbaf', '0xb5f5585d07dd3121', '0x39099d919a9a3433',
                           '0xaa31e0631af4715d', '0xaed0ee6513f2cd4a', '0x47c60ff2682d341a', '0xc7812f2b15b4d1c0', '0xfd13a34b8bdf9af8', '0x100ea11c5c02a404',
                           '0x2f0a1c653891e702', '0xd6d2b8ad02557ca7', '0xcebae0203537d09e', '0x829e335708b96814', '0x95e7f17e7bb094a6', '0x53541780a28f6e18',
                           '0x6075e3de5bd7e4df', '0x61f56e8ad7b19960', '0x6e4c9b37600f1298', '0xe7b01b104244bcd9', '0x9c59cbdbcc51730b', '0xbc47bb031af028cf',
                           '0x3677d3f2bd7eeca2', '0x5d3cb61dccac5d9e', '0x6d0b31a5fb3c271d', '0xb21f6400fd086c35', '0xa5fb3f7142e2d9fc', '0x49d215dc37a4313a',
                           '0xfd046175519309e7', '0xf37ffeb64a905ef2', '0x7c16568222e76963', '0xe0fbb7ddc23ecade', '0xc4bfcb6d955556e5', '0x7a9b4d3d8e70e092',
                           '0x8a30e5ff5d50ac6d', '0x1adc4117aca7caf1', '0xb397b866e8c18dc1', '0x0315877f5ab16f1f', '0xd79dc8738277eede', '0xf1ee68fd8c4d3aa6',
                           '0xcdd815ad10f3834e', '0x727f0450278fd96e', '0x05d8afec32159d95', '0x78ad7ee8c3005e00', '0x41c1f7322006f816', '0x1bf427789d4c9f03',
                           '0x22559a72310bc8fe', '0xc968299e1aaa9593', '0x272e87ff7e8ca57d', '0xd853ba580423f8b7', '0x25a6a2652962b61b', '0xd72766740e4bf870',
                           '0x99987cf5b4436055', '0x4244398c17c22202', '0xe71d4852d6bd938e', '0xa8124c28da8f5da1', '0x698aad54b6358897', '0x17eac6edeb5aa21e',
                           '0x5c79fd334ba05e3b', '0x27dfd5b99390ca5f', '0xe517455cdb5a27fa', '0xda6ee59dd844e902', '0x5eed7395c9efd87c', '0x84768c0f366370d4',
                           '0xc46e6a652e90ab6b', '0x7304ecb2ff74d8fb', '0x83fb32e11b5418b9', '0xfd626f0ca458a9ae', '0xd48ac456c9f462c9', '0x5128eb899b5f75c5',
                           '0x5ba2bdacf5ae830b', '0xb8bee4829965e53d', '0x47c114b4995cbc8e', '0xfa27bd1981b8543a', '0xb91bcb4485bc5b59', '0xc999ee357e5d0743',
                           '0x2173126bce0998e5', '0x49306fb62698731e', '0xa95a7c3f9576d83e', '0xfed02e83d4cb644e', '0xfac42a6f4a7f607f', '0xdfa297bb91b31272',
                           '0x0e2e3c036265540f', '0x9060f6606046fbf7', '0xfaa97293e53ff0b7', '0x28bb9cb0805584a6', '0x6c76dbf284b55b0b', '0x2b08abd4cb230179',
                           '0x9713b036303ff459', '0x071b9537f8addba2', '0x31cb52ff38df889e', '0x0f2757d0b09b6b30', '0x83c3771da4d8f83e', '0x5455bcbc815449cf',
                           '0x3b5aec0339c8bc05', '0xa023e8373d94ad70', '0xf98f6707b5e68e51', '0xeb0c99b28c5508ba', '0x8da4d717d6917f93', '0xd261a675ccaf0931',
                           '0xd5ac7aebd2b5ab72', '0x9bee6daeff38425f', '0x688011c60c30d6f7', '0x9c6b9936f6b3b9e5', '0x73bdd705b0ef2be0', '0x28289d4a28a54c54',
                           '0x52c4bbb7d087e0f8', '0xfd028b8920ef5e02', '0x3cdc0ff7e59699eb', '0xd6d948108134638c', '0xe114acaa4c3c7d44', '0x9f443556896ac48b',
                           '0xa546b2a580aa8ca4', '0x7d839e119987f989', '0x9101b1a8c4ad4469', '0x69a14fd05b19b55d', '0xf554d5b5618bd2aa', '0x5af442dd1fc7ff5f',
                           '0xe378d24d574f010b', '0x761aa0126e3bbb3e', '0x20f6d7fe7bf14d2e', '0x25aa59b22c9fbf84', '0x4f02ed1014fc219b', '0x82e28b79a0eef764',
                           '0x0d329d2cefe21731', '0x3a4ee27972d0dbde', '0x6e23cc36261cd6f5', '0x02ea8241936a6cfb', '0x55cc05da8fae5b12', '0xa90c564c08445fde',
                           '0x180f8e092fed112e', '0xd89394347fb37ccc', '0xeed6dd94e3077f04', '0x9b3d610eb0584ea4', '0x0573568abc4f5f00', '0x1d6c0c843d0d4dae',
                           '0x671fb868f854194f', '0x6437126fb961b1ec', '0x463e793dee4d9e2f', '0x76f0c73db26b157e', '0xb2c0aecb000f747d', '0xec7d1cb611a266d8',
                           '0x4fa4f66a60a36091', '0x826f76d6f80183ea', '0x2843f937fd6a675f', '0x984947368b15fe4c', '0x779372cb8e381b52', '0x13fe5bab707ea772',
                           '0x8e6e834aa2cd1289', '0x7d22216e61f0dee1', '0x245350de5cb46e4b', '0x9dbb500860cd6712', '0xbe597a8b4b069982', '0x3ad1b353edbaf673',
                           '0x667ef1006abcc989', '0x38e70f5c0d67908b', '0x95e48ba2454e460c', '0xe2a81cd03dead17d', '0x6b69a35eb55dacef', '0x5634d202b959d2a0',
                           '0x8a30d0c7f8c83dd1', '0xbf5a8c87d40706a9', '0x5ae5ef83e9ac0076', '0xb491df1aa73d6fb4', '0xe913d2e56bde6c13', '0x7a20706e10be6553',
                           '0xc0914b7b61c2231c', '0xe402818266090a19', '0x30e29bbc92bd9db6', '0x20ed8a2340989360', '0x0ee6b25adb7d8843', '0x2d2466efc9756196',
                           '0x3c3ca3f34074d640', '0x965cc36b32fbeaa6', '0x4e98b8c90139ef3f', '0x2d6f913039305ddf', '0xf19ce84275b3b415', '0x9778578df08450a1',
                           '0xf5813cde7940e9fa', '0x27ddb44c869b7490', '0xaf2eecbbbb197d15', '0x60722a845b50ac53', '0x47aea498ffc86edf', '0xa739f4ccd04a04a8',
                           '0xbd156b3f461d10f9', '0x3673e4ee07f55b4b', '0xea16bc46d7fda0a9', '0x9ed60fdc47c5e224', '0xf1e517356674bc62', '0x94ac118cb773c6d9',
                           '0x1846f2e1f730ca84', '0x0da8dbbbbfb7209f', '0x4592e046592644d5', '0xad7aa930d0d469ac', '0x99736d4e28861066', '0x9e636862e7596b6c',
                           '0x8f05eb07a269a38e', '0xd60215c99722304d', '0xa7114abea10880ac', '0xffd6a07c924f53df', '0x583bf00ff1ee3f81', '0x5383e8d7806dfa1f',
                           '0x46c4d34efb63f9db', '0xa9f56ca621f90a66', '0x958d68e21b36119b', '0xace22145470d8c30', '0x5921de12d02bc56d', '0x186a5f66f7e77137',
                           '0xa4068544766903df', '0x5cec9d8696fb83e1', '0xfb550b5b153acdcd', '0x20dafe1c3b31724c', '0x997137cdde38fd72', '0x1f6d9058b062b702',
                           '0x712d0e95a3c04481', '0xd3ddb1fbee50282f', '0xf46898bcb147f20a', '0x1ef0be8b7b50d90f', '0xa203b69049d27c00', '0x3718ef214103a0d1',
                           '0x6129a6307caa0a5c', '0x19b35e6a87c8d3de', '0xa850f00b52e2177d', '0x2e6ddb8d286f0b81', '0xbe22607525b0a81f', '0x3dde291194e0a586',
                           '0x3848c993fb25ff4c', '0xe8550d6fc96fc367', '0xfa4eafcb414335b4', '0xc9a12df85369d0e1', '0x0756b33d4cf9fdab', '0x41caf75b9b1e5154',
                           '0xa6d08d62b9f8c1fa', '0x139a4789d699ab85', '0x3b250d01c625e2b4', '0x79c2a0a694bc7344', '0x7a9634781feb0453', '0x28709070219c3888',
                           '0x18d43dc90c766164', '0x96b197a9d7fec243', '0x6fdb315e0b664e19', '0x2d5a72ad9ff0a223', '0x21a660dc694cad1a', '0xde66dbca71296555',
                           '0x8b9e2138082f39cc', '0x83b76f5f9019fa60', '0x6727154e298567c6', '0x8014b7cf50fcf44a', '0x59aecc78a111919f', '0xd580d1b6174962ad',
                           '0xe2127af8d8c6639e', '0x14689b44f07f27a7', '0x22860a42a7709db9', '0x313383d0d3ecfea5', '0x69dc82fe5e3cc50c', '0xb50650f38fcd8de4',
                           '0xc7297add6656b203', '0xcec8479a0b714f2d', '0x1d1ccdad0255fbaa', '0x99867e3b621f7d30', '0xd2a074f618f9ed42', '0x5e80ace956c30fd9',
                           '0x0930031426cda7af', '0x3b0d03a444d464ec', '0x02e8ed651effc795', '0x72191d54caf16c3c', '0xe473a3be39f0fa8e', '0x4914efcb54dfeab5',
                           '0xa21d9b8552313764', '0xa6cb35459cd95761', '0x03b8ce7c85abe70b', '0xf66d518698bc6eff', '0xe9079b2516ce426e', '0x6471c069e3c17550',
                           '0xcd64faef6c52643c', '0x4f963f7b51922df4', '0xf6009bd08c73c6d2', '0xc71d08f3d13de6f4', '0x3b1ed22f80fa82c3', '0xf1882a71ce2859eb',
                           '0xbfe279e8499f2dec', '0x54cb4fa6c6be308d', '0x6c3d82e4e9ed1d9d', '0x0ff589c6cbc212da', '0xb3514e7139cb0328', '0x2c53d223b5fb5a39',
                           '0x709cc2a80f049c41', '0xe8fb8d3130fcf235', '0x9c9040c07493bef5', '0xaf8e363e73b8b361', '0xa6e3c3aba13e09bd', '0x79dcc5f55ef2f040',
                           '0x0eaac826f504c07f', '0x92961be29e469a47', '0x0b534f28ff6d906d', '0xcf5ed6bb2c792d00', '0x1ec64ef488a8b24e', '0xd11859b8c56ab3ab',
                           '0xa48e86dae35bff75', '0x59fa8f477aca7351', '0xe70d8916c8ff3374', '0x60f79cb9198ad65e', '0xef8804c9febcea16', '0x94ebb692fb5d2fa8',
                           '0xb2257a02c0160830', '0xd09cb1b0513e78b0', '0xf9811869c819ce1d', '0x44e0d1445828d654', '0xae17216f4d20f631', '0x71171627c0193c68',
                           '0x469997e36229103f', '0xec4c9c9bb63a2ba7', '0x628dbef89ed49a13', '0x2b7a3b090e565df0', '0xfafc8c3584d01c52', '0x9dddee38bac55605',
                           '0x2eace0fd4bdc8f2e', '0x9bab98753169ef2b', '0x72151d0952d4796f', '0x48cb578a6ab90f3e', '0x554c30d0161710b4', '0x661dba38f827fbec',
                           '0xf877ace6428051ab', '0x4b485b8cc79d8fa8', '0x74566cb59791222e', '0x39fd592c33bc3003', '0xc9abe364462f3573', '0x1295898195f3b36b',
                           '0xca56b8e9b975c195', '0x0181fdaff9c10f30', '0xe2f0a7ca6bcff392', '0x101c1f38e8dd1a31', '0x3dd471d02454744c', '0x266d6c6913519430',
                           '0x1d0c774c31e053f7', '0x784b69b94ae1b40f', '0x4ade01e00964a69c', '0x78cf4e5889eef68c', '0x26f7c05ff2facc43', '0x3df47fba4095e9a0',
                           '0xdbaaf5f8c8d20dea', '0x0b611475faf422fd', '0xa829d7ce1d02ca1c', '0xec2104f2c96099cf', '0x5a8b994e05f70de0', '0x8552861229cbe819',
                           '0x57f976d342a40446', '0x0c50b26b8fd41dd7', '0x8f4a7b45af8da415', '0x88db23899c2db2ee', '0x2151520c1b4cc4ba', '0x078e6f60fd354bbb',
                           '0x3a034737d997b190', '0x1bc72398c2e17119', '0xbb556a68f988edb9', '0x4e56cc27d8b96076', '0xe6b057bd10954e3e', '0x96aeb5015844e919',
                           '0x5f244c6fa3f0e809', '0x561fab8847e58dea', '0xe016ea05acf432e6', '0x0bc460928dc229d2', '0x09adb5e8baa2b7a3', '0x62e144bd9e8b6eed',
                           '0x7a20dc37ccc7eea7', '0x53f0f051290e8ce8', '0xfffbf2ef9342c295', '0xc5c08db5b1e0c0ef', '0x6c813a08e5e52187', '0xdf3c8b2b30bd5710',
                           '0x00b8052ff9ed3bc7', '0xab4809bc5e153283', '0xbdaf55e55e5a946c', '0xc8ae40ffe329aafd', '0xc03db8737d5e9b0e', '0x111573eb26c19ece',
                           '0x6f21e1e5f038457d', '0x09aa79c6bf5572cb', '0x758aa3623eb60afd', '0xad78dfde49e9c154', '0x49394ac17a464193', '0x501987164c82506c',
                           '0xdc6bde1d3317ffc7', '0xa62aae96bc33c54d', '0xaf511b412091131c', '0x7cac9808671412ff', '0x741fd789fb29b2b0', '0x49a762ff7b1fabbd',
                           '0x04adb6fc05912379', '0x14772edd7d7f544c', '0x4062543d96637f8b', '0xa98e93e4ec0a752c', '0x419e5745a6372907', '0x221762f9de62d8cd',
                           '0x0520d8cb581b7ff7', '0x35f92a620ab3f59b', '0x050ae41494a0a27d', '0xbd30173dba7c09e0', '0x95b76cb9a4cacf40', '0xd8ca73b24ded4f0e',
                           '0x0ac67b34aecac78d', '0x7be7b4f6d85eb6ce', '0x887f5d9c98f3ccd4', '0x429a406291c1d58f', '0x13bcf186d5a050d4', '0xfd11e4b4c7939f69',
                           '0xdf681f54bc29bba9', '0x4fda999dc485474a', '0xd6e47cf174037c2f', '0x41301e4b94127914', '0x8acd75a2e9a2f121', '0x57d7c037fed25bd7',
                           '0xafaf80639a2aaec1', '0xa2649a6cc4088945', '0x17a3332b2a7c8646', '0x170f082cd1466641', '0xded4aa0c8927774d', '0x0a2969d6cce86e0f',
                           '0x693d0b3ee4e55638', '0x5d9e689eac721c7a', '0x1a129e54784a71f4', '0x8dbc32d3877435e5', '0xa219d6f8d67fb022', '0xde823f0c6d7709ec',
                           '0xb377effc344827a3', '0x9df05eb0ab57d1ee', '0x789e366e3b504906', '0x704a90ff93a4e052', '0x85cfed78eb1d7ab1', '0x9d6a8656f295d65d',
                           '0x6b26de5af87d1f60', '0x0d9673a9705b3470', '0x2cf7d74f496cf38a', '0xbc6b922a0ec7009b', '0x5e95a43c1fc2ada2', '0x93d4969823a82170',
                           '0x953bc3e78eac5f99', '0xb33d84f1dd399d57', '0x0c3475cb0974502f', '0xb6917879b1f8b749', '0x641a76bcb920c65c', '0x34611e733e6ef5b8',
                           '0xbf737a4fc375cfd9', '0xf2f9638aa8f154a9', '0x46f503e21d935d21', '0x53600931ac352abc', '0x2764f7e2e5237664', '0x1d6bacf9c6650060',
                           '0xcf4bc37bf99a4e6b', '0x34802651fea4b8b5', '0x1cc4fc6478c6d11f', '0xc56e321f654bb5d8', '0xa6d9cdcceeb5c8cc', '0xda766866344c37ef',
                           '0x6a90d4a70ce6b086', '0x035b50d7743c2306', '0xd906110ba001a3ce', '0x33a01e3f6cfab462', '0xb5b532f25dbd9466', '0x9ce78a37168fcd38',
                           '0x822e446049a84c39', '0x874113bb78fd52be', '0x72a0c4d7aaab60fd', '0xcd2b89710f9423d4', '0x0216fe71bc29d813', '0xd4d2d065e4ad2233',
                           '0x305d55187271839d', '0xf2a44cc81e6f4dbf', '0xacc1da2b5a9b8f66', '0x0154a616803e72cd', '0x3fc328932f58f585', '0x197f581291038e85',
                           '0x39750fd4c813c6b0', '0x1c2f50bf687d1373', '0xb1d355cffcde7559', '0x14c772d3a98d3162', '0x11849c30d1c92cd7', '0xb5cfd644f687e777',
                           '0xe662fe6d83e1f722', '0xeb65e48248913f90', '0x88089e653e075f5e', '0x93fba0181750da8c', '0x7a522cac2f8e851f', '0x7e1f8d0115cd79d6',
                           '0x55008c2f99027408', '0x2d3287c0fecb1991', '0xa22eead2131972c0', '0x6dcbdc57ea9c4126', '0xc5577594c155ec40', '0x044fc62405e8998d',
                           '0xe3304c9597934077', '0x0b1bec02c7c4da46', '0x8fd0ce31d874b415', '0x9576e4c579e62946', '0x974c1306045a9c59', '0x4d83760cfd572ebb',
                           '0x5be607bb8bd5e3b0', '0xa5bf00b8cee12762', '0x5d86fc92254bf1a6', '0xbb273b9aeff85b27', '0xb9af0c1c79b1e711', '0xe6583740574607e3',
                           '0x1e7cec13824741eb', '0xaedcb4539357df03', '0x30ffba4475593e5d', '0xcfb5db962e4d9e6f', '0xb8897614b54b3a1a', '0x148ff920c6ed9022',
                           '0x920b1042483a8f04', '0x187035c46c96c545', '0x347087af158ef7b5', '0xab402ab8e746c824', '0x91ede8faa74fb33b', '0xc8c6c501b82dbcf0',
                           '0xd1f040a1fa2747bd', '0x7dcc2d38ec5840c5', '0xa21126cb270c510f', '0xfaae1c31ef073c32', '0xdd8e6b07dc91e942', '0xb624a110f8cec227',
                           '0xaec163de17b50d75', '0x678539dd6657647e', '0xf5472b15e51ca3ae', '0xf9bd4fae8c4e0b44', '0x90d75fb40243a42d', '0x06cf8cccdb5eff03',
                           '0xec36c5ec208bfe45', '0xb75ca64c88217854', '0x5a4bc3334e241d0e', '0x2b23492e6063f85a', '0x7b07e58b81603e5a', '0x541af67609b9d04e',
                           '0x5cd610b1f6246f85', '0x557ca8c4fd6776ad', '0xd97c831c21e88b90', '0x174f7d54d9d9ebe9', '0xf381dbbf3498b78a', '0x986f29f1dc6e598b',
                           '0xa4718a7b5e12563b', '0x1c787a410022f5c4', '0xda7395c3602c0e8d', '0xb5e17ac67f3b33c1', '0x0f3794f298c7d83b', '0x44f2e69345b39d48',
                           '0xd82ef1a33153e174', '0x303d6d48e5ba749f', '0x534d65a3905f9baa', '0x23a024244f9ad197', '0x1ee65c492e0a0e8b', '0xb7e245c51d7100f9',
                           '0x761145af8b8c62da', '0x8cc36f8952dc42c8', '0x2b7e69e7a5ea4a0f', '0x72ca1d2aa1d2d24b', '0x35139f449c283994', '0x36702c2161c46599',
                           '0x3b4e0430e0ef8417', '0xc9176d096a15fbec', '0xf83041f965907f2c', '0x9a7470d3dd819638', '0xc0cf55fe02efee75', '0x582653ec01605c82',
                           '0x436f4e4a8692b837', '0xc705aaeb883b7a3c', '0x6f73d2f95c563b8e', '0xa82726ad84b40689', '0xd52492971accce8b', '0x64a4790fa27a593d',
                           '0xd3eab2d93291c84a', '0x0cff7054ddd38e24', '0x1b3fde4439d1a41b', '0x4899536f581c6130', '0xc0dc2a69b29afae8', '0xb00c7556fc92a6dc',
                           '0x34d60584c0d06da2', '0x5b47803e783bcdb0', '0xcc47dbfd08511624', '0x159df2d8cbc557c0', '0xf25d94eda71ee8e9', '0xd65814552132ff4f',
                           '0xa40e83a8323bf379', '0x092b4aed35d1f724', '0x675505ed1a7ae4b1', '0x651e165e37ecadfc', '0x547c0c5d44890135', '0x68f3f86b14571bef',
                           '0x69b3eabdb1f93e06', '0x8e9446a2306273a7', '0xe56bc7dd7e269d86', '0xd268629e15540a61', '0xcc1ae494f6cbe85c', '0xf9b67e546f345d61',
                           '0x1f2a1dcc922535ab', '0xcb32f767dd99c7ea', '0x7c5484ced2210dc2', '0xee7e959891973ed7', '0x5a8854c0aa276e78', '0xebbd2c49615891f5',
                           '0xc3e702e07c097227', '0x14062e4969cfd241', '0x119201016761e94c', '0xdeb61fcfef6c8164', '0x4728d6620731f961', '0xd35f176670a0fb71',
                           '0x1c389c333b9b48df', '0x3a2f748490b79666', '0xee1cdc0805cb5f53', '0x8f671e24771a48ea', '0xad05502389b8498c', '0x1e180b87e426c7ff']

        MDS_matrix = [['0x70e6dae2c651cead', '0x090e1669a71a5d00', '0x850eb1097fab4a21', '0x0b897348e7e0fab0', '0xdba1e3e5b76ed64c', '0x3334f13fa046b4ad',
                       '0x8a4d7cf4f0429ffb', '0x19ea5fc1afb8c40d', '0xbc9b82c52e2d16d3', '0x6ef233462dfb9102', '0xb78f9a4aa5692674', '0x137434135cab157a',
                       '0xdcfc4fb1fad92667', '0xf2da17d8ccaf5dba', '0xdc562eb3b775a230', '0x3a579ccd17e69b21', '0xcd4371daa1f50ce1', '0xf3fb536f0880da4b',
                       '0xd4c0d70cbe266d00', '0x922f62855fcdcccf', '0xf2587b5670e3f932', '0x83cbc18d3068858d', '0x42418957cdb87f03', '0x8a1c2e26886dcc62'],
                      ['0x59ff431e0b5017a3', '0x5f5653f6d4b07aee', '0xf3a7fabec4bfaa90', '0xeaa1c6cf8a5f93b6', '0x640fe1aec663543c', '0x5e8b2eb00c0b8f20',
                       '0xff0e9e271c3cd79a', '0x8f893f3bf126360f', '0x09ace012c2348c75', '0x53fddfe811ff2173', '0x42b52ba39e72e1af', '0x2d4ae7306cd3dee8',
                       '0xcca7a772494dda3f', '0xc3c21065f335c8ed', '0xa38e5f985541602e', '0xcf88ae035fab200b', '0xc3e845fab9e1952b', '0x7e80802dab7470dc',
                       '0x3394d8795d6f79d9', '0x700e544671622092', '0x8c106de82508d7b1', '0x3456079cc49e452c', '0xb87cb49c6e5ec4ff', '0x72f947daead3c78e'],
                      ['0xaa12114e4439ba64', '0x57de0d281134d6cd', '0x0377608221c83b90', '0x6a0b326610dc231d', '0xe09d23f52773557e', '0x0b6c555d16c9698f',
                       '0xd3624f92c8712ac4', '0x4c1b3aa96f6afe15', '0xe04985c3f61d5725', '0x2cd40901905ea647', '0x085e32b7ccfaeac6', '0xe2a7a06ec82510d8',
                       '0x25e8ab1476f3f970', '0x977a803a3fa88d09', '0x747022bdb92cd39d', '0x7ee29e2461848828', '0xbca7ed86abd40b1f', '0x4d8eaa622dcd79af',
                       '0xd3abc7ebc94290b6', '0xa6bc3eed3a521f15', '0x116e2b29a9e82c27', '0xf07bc2c96b13d236', '0xac1a30f50cbbcb0c', '0x5337477bb9fe373f'],
                      ['0xbd456704024b80ee', '0x77bb0c1a330f047d', '0xcdaeb6a71e161841', '0x5e6bde7e309579c8', '0x7b0d9d6d914f5550', '0x1108e728dad5ef99',
                       '0xabde85b0948b686f', '0xd0cc4a661ba7b46a', '0xfaf9bde12750e80f', '0x2cd16331ac48ba70', '0xbcc8becc4ed494a0', '0x00ca4c234254abc9',
                       '0x2c0188455a6585c5', '0x1ac76c144a91238a', '0x70b952f793ba821b', '0x33da01a130d2ffcc', '0x3aa3ecde16bb3d7f', '0x475e24ae547149ab',
                       '0x7e8e4d93128fe99a', '0xdeb9d09eb26db2c8', '0x041b350f67f0bdf7', '0xf0b3ced1cf3aeb20', '0xa94fae442109b2de', '0x5148d587558e451c'],
                      ['0xe20ec1f1d0dccdb4', '0x56bb8d026b1d8ca1', '0xdd35d5235b2dfbac', '0x19e54fe669a12e3f', '0x481d050f6bed5d15', '0x6d84f03061d0650e',
                       '0x53f09bc85e099939', '0xc28dfaa7e1d3959e', '0x582893256437308a', '0xbc5cced5d7ed3024', '0xf902a4934b46eb74', '0xc16a119276c6f4c2',
                       '0xd05ecb6b8d31e808', '0x9e84930796cfd5c7', '0xf14cd791e6cbb148', '0x97b57db2a72dcc56', '0x9f8fe7db8263766b', '0xb216cf3a71cc1261',
                       '0x45a818f076cca2d4', '0xdb0240ada8013a0a', '0x540b0e6f28ef9c93', '0x19d2fb48f3a9c08c', '0x14cf42a420aa8721', '0x383a092d2f33e9aa'],
                      ['0x9290393c5fea5212', '0xd93945ba33122406', '0xecbe7af7a0dab614', '0x7db4d64074d583e8', '0x308ed70dfba59804', '0x08450614e209de8c',
                       '0x76d7443c773e270d', '0x0074410e893a94d8', '0xd172bb93833466f1', '0x9a8719e0b822659c', '0x9f7a74da14cad5a8', '0x28502f3040346c46',
                       '0x16c2eeee1dae9a39', '0x86bc605e13beafd4', '0xa189359049c3bcec', '0x80a28346ef3a936b', '0x4cfddbf3af068f8b', '0x5ac9909428439f31',
                       '0x8e4e25e3e69cb21b', '0xc1d04d6ff1b52909', '0x6293b3dc21f82a0c', '0x6a6b37adf449ff61', '0x4160900d97137082', '0x727458c6c77fe530'],
                      ['0x906d8c76a5bb02a8', '0x16c4e6d73c27e202', '0xcac60c15632c6ce7', '0xb47d85d9b7d89577', '0x29a1d5d5fe9db3ec', '0x7131f056111d8915',
                       '0x991392cccfbd5ee7', '0x2ef2dc59457ecbdc', '0x81377100a281c260', '0x167e27dc5f056066', '0xba1577fc36f0a96f', '0x7f9170c61554e917',
                       '0x9150ace40acd53ba', '0x752a74387c859824', '0x188e1b22401bf247', '0xc68d951fcfcaaa0c', '0x28218483354e1132', '0x4b96077539116d04',
                       '0xb64b6816ef57177b', '0x2e71b955728c25d6', '0x9488b974d4dd5b5b', '0xb6c5224b98d7c036', '0x1c24e35592b63675', '0xc91e8da2f57a525a'],
                      ['0xe85c03395c0200a1', '0xf6bfcef1d409bffb', '0x0196b09f44600604', '0x89a41dae2da87b49', '0xb97bc50b093755da', '0xb6eb65ea6627b28c',
                       '0x7a440371db7437f2', '0x5c68e5fe22d800a4', '0x5a51501da57e4f99', '0x4d515fca19eb89ef', '0x2c93cf282add0820', '0x292d273173c66e5c',
                       '0x50a3310afff19ced', '0xf61c39a773dca545', '0xcd072b51d5b0903b', '0xa833ebcc5f431b26', '0x5b6b4c249593f1d7', '0xdad0a7ca0171fc4a',
                       '0xbd56470cc249d0a3', '0x051a6ff128ed92cd', '0x16f403a09d6ebf37', '0x0d72cc8a94b9ede3', '0xbc71f787e8614720', '0x9aea3ad16887df2f'],
                      ['0x53b29e8044fd73df', '0xf7cf6c83df0e8fc7', '0x70e3be85e7abdac2', '0x2f9d51e23ad33a2d', '0xfb4492e97f6fde3a', '0xeb86487afb325322',
                       '0xa430c39b0557dbf3', '0xfbc2d550b55e5d48', '0x537eb39ee6693c0d', '0x40c4ec642d25c034', '0x604f154a35afc282', '0xa714bda94cfd4c39',
                       '0xcd6a9134908edf03', '0x9acef696f244340d', '0x9309982069ef312c', '0xa63124f8306a2484', '0x242a061483d71f89', '0x0d3ac433a626f18d',
                       '0xc63372098c346aa9', '0xd07fa091cd4972c6', '0xa224f0a1c9631161', '0x63f048b3771c41e5', '0xe2817c6c0c265bd4', '0xba7cadf0dcdc7df7'],
                      ['0x8a3d3ba02a08c8e7', '0x3f8f8c0b93f58b07', '0x46a914cfaa539ffb', '0xa960b80187ddbbb9', '0xc82096cacfdb76e3', '0x09a8a4319261fb92',
                       '0x81d077321be2dff1', '0x6e3071b7f9a8aaac', '0x6706f82ee70f8495', '0x6a43592cb42d98b6', '0x92d4015f02aff96a', '0xe2e5ba3897f2607c',
                       '0x5d2963620a32c819', '0xe2d0e199b463a622', '0x2493a5ff19745ffe', '0xb3deebc1108cadd2', '0x115c60690d06ce7a', '0xe9b1ef8fefc04991',
                       '0x4f798423a6b7a779', '0x7f976b5576b34d22', '0x3c8bd94308dda075', '0x5178112ba1b01e33', '0x3537d202f9482495', '0xec2ea2cf504c8319'],
                      ['0x68d9792f24056e97', '0xc4866bde9e51a4c0', '0xafb004092bd661d1', '0x89258668a873959e', '0x1f66032575da5d81', '0x2f5aea7a02be42e4',
                       '0x06980b9291234b40', '0xa194dd243299e88c', '0xe81d7d3fbe1c2119', '0xd2938ebbe6f286f4', '0x4be0739bcfdffcc3', '0x21fadc0da8c8fa5a',
                       '0xc048165ce8f77049', '0xbae3908d94440b22', '0x712c6253e40372de', '0x1b2c51b99430d569', '0xf765ea0171dedf8f', '0x8570b03fa7bde5f4',
                       '0x1d051cfd9f4abed4', '0x4d82838ff0098c48', '0x30375ad96d9ef6cc', '0xc0047722489f8de4', '0x9cc440fd22d8f3a6', '0x46ec4683066fa64b'],
                      ['0x414e3ea5c7d31fc7', '0x3dbfa02b58e306d2', '0x0012c092d2ff92e1', '0x8f0da720beed5e94', '0x016a8b827f35a15c', '0xe534011671c8f273',
                       '0xe438115add5f9d52', '0xb88fac38660cca71', '0x7777bc3d77a0c74e', '0xcff482b7851f4aaa', '0xd841eb8a99602bd5', '0xbb50b08f478775fe',
                       '0x3e3d4e9ccdb95b9c', '0x04c994e0977ae208', '0x97250390de2f9d33', '0x1859f684202cfd22', '0xf423d2f16802f031', '0x3cfe68c0bb1c7d2c',
                       '0xe8c487e32ba56675', '0x318c69e0288dad4e', '0xfee4a069ade5cd2e', '0x2b09bd17e383def1', '0xf4d60ebb9f715881', '0xd379aec9fa0b4b2b'],
                      ['0x220c90edf0f596f8', '0xf682a229e08c50c8', '0xd1852b2130e9aaa4', '0x83fb89181aeaeb9b', '0xaf7fa83e2651bed8', '0x13886e514a80d384',
                       '0x6ceaf0bb1d62a1ae', '0x6ed2d8fab133536b', '0xf3606bd92537b5b8', '0xb5e55921ea88c95a', '0x8d145749bf1d397b', '0xb96932834ff642f2',
                       '0xffa6a68e7dc1778f', '0xe81d7ba99227c61a', '0x467846b725b93eaa', '0xc680395a9d8f6043', '0x80babe12dedd445c', '0x482f332947be96da',
                       '0x35161fa17903a149', '0xb5b42a12e1148f67', '0xaffeef3ebee87966', '0x20ee335491a73e40', '0x7e5fb9d88533cccb', '0x9b1fa3018283895b'],
                      ['0xd66a2ab2aba8b024', '0x47d826fa53ab2f76', '0xe473cc68eb366312', '0xa94ecebbac6b46b5', '0x90f44a19e9f1ca8c', '0xd2e4b03d37caf066',
                       '0x98a24a4444cae665', '0x795480f4af50f079', '0x02590696ead689f7', '0xd85c11df41c246c1', '0x95d90a784213a76d', '0xaa55b3bfff175079',
                       '0xb4a7d88259d019df', '0x17400692dcadd17f', '0x2cba36e2ac25ca62', '0xa70268f2f600dbbe', '0xb3df8e0052e89ed8', '0x654bccae501033c4',
                       '0x4d1da3b20c7edd1d', '0x09e6d695650f6601', '0x3b0baf129b789800', '0x74f621524b786f34', '0x2a52ccf6d9ab63e5', '0x97487b87471144ba'],
                      ['0x7f3c77b30f7a19da', '0x57e59eb0d4a68db3', '0x86c94608cba154e9', '0x07ce7176ff94f679', '0xf269367beb91bf4e', '0x4fec3bd49bb5160a',
                       '0x8e228735eb17d66a', '0x39392005a88ee999', '0x37fc74cee03968c6', '0x9c261ef8afd13142', '0xeec62d5c7d956499', '0x432801d5ffee63fe',
                       '0x45111b3ce31d3738', '0x5ea769a9e0cac6ae', '0x892be71f8275b77a', '0x24b06878bb40afed', '0xfd25a7441057bf85', '0x1b5ad44fcce50488',
                       '0xf81b68befc1434e4', '0x869a134b59d9186d', '0x014519262bed14de', '0xea0429937e292811', '0x68015ad8fe4def55', '0x948dc5cdcd5bee43'],
                      ['0x83a9e00f6c5a20ee', '0x20aaa2e1dbbcb9ff', '0xd17a9f73bda9fc90', '0x038f70dc0c7f7eba', '0x055440a7d0a35e3d', '0xbd5ac63a13d1a7c1',
                       '0xec0ae61b6b121c5a', '0x056cce03061e845c', '0x569d963f9baa8e5a', '0x7b87f079d4204952', '0x01eec56cc50f6307', '0x1244a3ffa63b8f05',
                       '0x7a58c74ddae3ea96', '0xa983820d2f4aed46', '0x3d6ad347f426f308', '0x67d756082adbb51f', '0x4c7674aaeb95d483', '0x94157add6e435959',
                       '0x5857b8a734fa5629', '0xda5c0233dd1388b7', '0xf7a414fceb576f28', '0x7bb8becde7f68858', '0xae53c33cd9af464d', '0x2eee5f63c13b4d8f'],
                      ['0x1df78287fa15da95', '0xd988cdf63a39d20b', '0xd3a6412dcd61928d', '0x48047d7db2182fb7', '0xd1bb36f16d0635ab', '0xaa67bedbcbb25902',
                       '0x65f861b4872e101e', '0x2ee46b2125130756', '0x3be2874d7de0ae0b', '0x9c30d302410d29d9', '0xd3d06d877e43e671', '0xaef252790b68a6c6',
                       '0x9bbb18baa88453c8', '0x96efea746e5a9715', '0x845da562c843e927', '0x1acde58ead686030', '0xb482495c07b2729c', '0x8ed1fb98333d28be',
                       '0xb5254c885a6f71e3', '0xcf9beef012f23fcb', '0x8999fcbd397a5930', '0x625448ae7510ca03', '0x5758f7704c27f739', '0x213b1f365e92efae'],
                      ['0x75b99a800f6a4e50', '0x6480016a5692c75c', '0xa1b8e0944dbf341d', '0x9d8a004f8b956f3b', '0x4c06adc09d37c7f5', '0x52bceba90cc316ef',
                       '0xa4c726bf0a05c621', '0xa25fa8b92fbbee55', '0x722b97245d3359c0', '0xb7a455711a461a0c', '0x231cbb34de2a15fe', '0x7cec97f425eb2d45',
                       '0xb84585a25203a89a', '0x77aba4c7e88873f1', '0x37fe478b2c36cf66', '0xcb6484b2339f5f8e', '0x9d7bfa01a9e43ecf', '0x6e0ab9fcc52a6de5',
                       '0x0cd364e0a15796e1', '0x05d93140e2e3f2ca', '0xe204443778179d0b', '0xbef305850f048544', '0xd32256924554a49b', '0xc53511ffa12bb90f'],
                      ['0x24963e56058f634e', '0x42ba953bf6a2ebe4', '0xf59b3de68f6e561f', '0x97fde1b7e2e04fa9', '0xd54550d47e251af5', '0x06d59e915cb62071',
                       '0x3fb9da70660121f0', '0x9c6d745cda9317bd', '0x9b2e7bad646b7572', '0xeaecc8fa9e3f8ca6', '0x86da1cdb3cfcc903', '0x7d89bccf99ca4618',
                       '0xc424b3165b1272c6', '0x655f29202ed109b5', '0x6084931c4c587edd', '0xbf254b666533c51f', '0x6986d415ab4569de', '0x84c5542ce3d641e6',
                       '0xbecfc4b066cf816b', '0xb8c67054069cbcf0', '0x0c104c400ca7e269', '0xacd24cf52548e6c0', '0x539da2943a2cea96', '0x4b34154f23ce7f50'],
                      ['0x27a8fcc9a30540a5', '0x2a384863fa279560', '0xd30ad1b8bb0b5e63', '0x2e86af6a6f62fa02', '0x34bca2387740fcfa', '0xbfb4397008b15dce',
                       '0x14a5bfb5f0dc9d97', '0xe4649e64d9177252', '0xd7be1ade0ddbc8b6', '0x390a00e89f5cbcf9', '0x4d72acfede73bbb0', '0x187ee525fe64a12c',
                       '0xaeb1ef1688d202d8', '0x5be593c3c65b0667', '0xf3aa608de6ecc65c', '0x9d7126e3db70b9f7', '0x2c64d046e025840c', '0x415d660d4c1159e0',
                       '0xff20ed0db79423b6', '0x6d0d1d2b46e267a6', '0x33bcd8b3cb1ae3c2', '0x3ccf87b1d6f07a52', '0x6aa98e243986b159', '0xacea4c929bc468f1'],
                      ['0xda6bb46f0b2af6a8', '0x67d0fd089cc0898c', '0xb7dd68a9042cb514', '0xcdf03ff3c7130f3e', '0xffd80a8c40d6ae3f', '0x4a44e7f5385c546c',
                       '0xb129828ecd7e97a5', '0xbaf520f816202bee', '0x35706f5a82d07680', '0xb29eab3da9398698', '0xb5992f06769f0df6', '0xf83e56af0cc2860a',
                       '0x3378bd8b7bbd925c', '0x78cc26b72180477e', '0x7cfb9d3c73b4e3c6', '0x0307a503873383ed', '0x4f8ddac642662c7b', '0x880a2b8923b753b9',
                       '0x555e02695ba71c4b', '0x602bbaa3ae7f3df3', '0x89c865c1b0286a0f', '0x519c7245c1b05972', '0xb4c9cb14d4f5cb27', '0x9fabb53b3093a0c1'],
                      ['0xc3255de2a5e262f6', '0xb784448972fb2770', '0xa4ea00d549571431', '0x45a22c337fd9e7b0', '0x287182295a73e5cb', '0xa24808a6cd756b23',
                       '0xfd80b40176916b20', '0x385c2c05a01e88c7', '0x871a4fce2bf9da58', '0x38be6874cec2dfab', '0xb5b845b9dd7e6c7a', '0x2ac37898d7ab3b6a',
                       '0x0c220f53bdce7b01', '0x5a1245438b2db20e', '0xd334bc485d92f3d8', '0x1db892c2bc97cb0b', '0x5a238c35ee29f12a', '0xbb640f62634add31',
                       '0x9ad6871d056d0e7f', '0x6a6651c733137dcf', '0x34d5c1babf149ef7', '0xfe3edad768e25afa', '0x00cf7b9294eac04e', '0x8427ba6d9dd6193e'],
                      ['0xfce915ab6e25b3e6', '0x3688b8fa8c9f5f2c', '0x18b9f2b3bfe960f4', '0x326a77fae4be97b6', '0x96b1cfe94cbbb3fe', '0x14faa9260126b6c6',
                       '0xb1247f567f78c70a', '0x385d2b599cb24e41', '0x177c0ac30bb6dfde', '0x06c45afb8fe169a7', '0x774b3f49d7b331e5', '0x043bc5b74dcddd15',
                       '0xd6686614e69af832', '0x00b13abc2a3e3af5', '0x965b038aa331b415', '0xf61b80d291a40f3e', '0xdf59a4d74a728fd7', '0x25e58ab87a486039',
                       '0xbf553e8dc30f8f85', '0x1d479d64073d2f92', '0xac79c8b3ba7185da', '0xf64bcdb3a4250bf6', '0x31cfe575eaed24f3', '0xd71997c2aeb6ea3f'],
                      ['0x4bf704fb6a8f8d11', '0x58db2b3041328f85', '0xebe72c913f9abdd3', '0x46feb18d627d5bff', '0xd03e70bc1e79149d', '0xe5c1990fb10fd8dc',
                       '0xd159b10ee894d37a', '0x245b633f6d5b526d', '0x411fa8aba6831734', '0xc7ae395a1329b0e1', '0x06116b8774d84f8a', '0x293107b5bc6c5637',
                       '0x57d15c428b496288', '0x65145619b98d0cb3', '0x9b4a4f48dde636ba', '0x08740a600dc09d46', '0xbb132862b24cdd70', '0xf4547a7a98c78c49',
                       '0x75d6aade510d3184', '0x78f002115511f2e9', '0x61554fca09413122', '0xc6758a78edfc076a', '0x993dc19cb110e565', '0x6b5259f029a70694']]

        assert all([len(MDS_matrix[i]) == len(MDS_matrix) for i in range(len(MDS_matrix))]), f"MDS matrix is not square."
        self.MDS_matrix_field = matrix(F, [[F(int(MDS_matrix[i][j], 16)) for j in range(t)] for i in range(t)])
        assert self.MDS_matrix_field.is_square(), f"MDS matrix (field) is not square."
        self.round_constants_field = [F(int(r, 16)) for r in round_constants[:(R_F + R_P) * t]]
        self.round_constants_field_new = self._calc_equivalent_constants()
        self.round_constants_field = [self.round_constants_field[index:index+t] for index in range(0, len(self.round_constants_field), t)]
        self.M_i, self.v_collection, self.w_hat_collection, self.M_0_0 = self._calc_equivalent_matrices()

    def __call__(self, input_words):
        return self.perm(input_words)

    def _calc_equivalent_constants(self):
        t, R_F, R_P, F = self.t, self.R_F, self.R_P, self.F
        constants = self.round_constants_field
        MDS_matrix_field_transpose = self.MDS_matrix_field.transpose()
        constants_temp = [constants[index:index+t] for index in range(0, len(constants), t)]

        # Start moving round constants up
        # Calculate c_i' = M^(-1) * c_(i+1)
        # Split c_i': Add c_i'[0] AFTER the S-box, add the rest to c_i
        # I.e.: Store c_i'[0] for each of the partial rounds, and make c_i = c_i + c_i' (where now c_i'[0] = 0)
        num_rounds = R_F + R_P
        R_f = R_F / 2
        for i in range(num_rounds - 2 - R_f, R_f - 1, -1):
            MDS_inv = MDS_matrix_field_transpose.inverse()
            inv_cip1 = list(vector(F, constants_temp[i+1]) * MDS_inv)
            constants_temp[i] = list(vector(F, constants_temp[i]) + vector(F, [0] + inv_cip1[1:]))
            constants_temp[i+1] = [inv_cip1[0]] + [0] * (t-1)
        return constants_temp

    def _calc_equivalent_matrices(self):
        # Following idea: Split M into M' * M'', where M'' is "cheap" and M' can move before the partial nonlinear layer
        # The "previous" matrix layer is then M * M'. Due to the construction of M', the M[0,0] and v values will be the same for the new M' (and I also, obviously)
        # Thus: Compute the matrices, store the w_hat and v_hat values
        F, R_P, R_F, t = self.F, self.R_P, self.R_F, self.t
        MDS_matrix_field_transpose = self.MDS_matrix_field.transpose()

        w_hat_collection = []
        v_collection = []
        v = MDS_matrix_field_transpose[[0], list(range(1,t))]
        M_mul = MDS_matrix_field_transpose
        M_i = matrix(F, t, t)
        for i in range(R_P - 1, -1, -1):
            M_hat = M_mul[list(range(1,t)), list(range(1,t))]
            w = M_mul[list(range(1,t)), [0]]
            v = M_mul[[0], list(range(1,t))]
            v_collection.append(v.list())
            w_hat = M_hat.inverse() * w
            w_hat_collection.append(w_hat.list())

            # Generate new M_i, and multiplication M * M_i for "previous" round
            M_i = matrix.identity(t)
            M_i[list(range(1,t)), list(range(1,t))] = M_hat
            M_mul = MDS_matrix_field_transpose * M_i
        return M_i, v_collection, w_hat_collection, MDS_matrix_field_transpose[0, 0]

    def cheap_matrix_mul(self, state_words, v, w_hat):
        t, M_0_0 = self.t, self.M_0_0
        state_words_new = [0] * t
        column_1 = [M_0_0] + w_hat
        state_words_new[0] = sum([column_1[i] * state_words[i] for i in range(0, t)])
        mul_row = [(state_words[0] * v[i]) for i in range(0, t-1)]
        add_row = [(mul_row[i] + state_words[i+1]) for i in range(0, t-1)]
        state_words_new = [state_words_new[0]] + add_row
        return state_words_new

    def perm(self, input_words):
        round_constants_field_new, MDS_matrix_field = self.round_constants_field_new, self.MDS_matrix_field
        M_i, v_collection, w_hat_collection, M_0_0 = self.M_i, self.v_collection, self.w_hat_collection, self.M_0_0
        t, R_F, R_P = self.t, self.R_F, self.R_P

        R_f = int(R_F / 2)

        round_constants_round_counter = 0

        state_words = list(input_words)

        # First full rounds
        for r in range(0, R_f):
            # Round constants, nonlinear layer, matrix multiplication
            for i in range(0, t):
                state_words[i] = state_words[i] + round_constants_field_new[round_constants_round_counter][i]
            for i in range(0, t):
                state_words[i] = (state_words[i])^3
            state_words = list(MDS_matrix_field * vector(state_words))
            round_constants_round_counter += 1

        if R_P > 0:
            # Middle partial rounds
            # Initial constants addition
            for i in range(0, t):
                state_words[i] = state_words[i] + round_constants_field_new[round_constants_round_counter][i]
            # First full matrix multiplication
            state_words = list(vector(state_words) * M_i)
            for r in range(0, R_P):
                # Round constants, nonlinear layer, matrix multiplication
                #state_words = list(vector(state_words) * M_i)
                state_words[0] = (state_words[0])^3
                # Moved constants addition
                if r < (R_P - 1):
                    round_constants_round_counter += 1
                    state_words[0] = state_words[0] + round_constants_field_new[round_constants_round_counter][0]
                # Optimized multiplication with cheap matrices
                state_words = self.cheap_matrix_mul(state_words, v_collection[R_P - r - 1], w_hat_collection[R_P - r - 1])
            round_constants_round_counter += 1

        # Last full rounds
        for r in range(0, R_f):
            # Round constants, nonlinear layer, matrix multiplication
            for i in range(0, t):
                state_words[i] = state_words[i] + round_constants_field_new[round_constants_round_counter][i]
            for i in range(0, t):
                state_words[i] = (state_words[i])^3
            state_words = list(MDS_matrix_field * vector(state_words))
            round_constants_round_counter += 1

        return state_words

    def perm_original(self, input_words):
        t, R_F, R_P, MDS_matrix_field, round_constants_field = self.t, self.R_F, self.R_P, self.MDS_matrix_field, self.round_constants_field
        state_words = list(input_words)
        for r in range(R_F + R_P):
            state_words = [state_words[i] + round_constants_field[r][i] for i in range(t)]
            if r < (R_F // 2) or r >= (R_F // 2 + R_P): # full round
                state_words = [state_words[i]^3 for i in range(t)]
            else: # partial round
                state_words[0] = state_words[0]^3
            state_words = list(MDS_matrix_field * vector(state_words))
        return state_words

class TestPoseidon:
    def __init__(self):
        if get_verbose() >= 1: print(f"Testing PoseidonMinVar…")
        assert self.regression_test()
        assert test_poseidonminvar_last_squeeze_poly_system()
        assert test_poseidonmindeg_last_squeeze_poly_system()
        if get_verbose() >= 1: print(f"Testing of PoseidonMinVar completed")

    def regression_test(self):
        poseidonminvar = Poseidon()
        input_words = [poseidonminvar.F(i) for i in range(poseidonminvar.t)]
        expected_output = [2395630374575380282, 1615974500016672975, 6465667013928772570, 15109795371388674146, 32373165242398276, 9330959482039670060,
                           2282718626378751914, 9135548066699070411, 12944928807956425561, 7163864101456107046, 11238787894371406199, 5127616110315773831,
                           686796029394435381, 10252555620017577956, 4049365281189477258, 12051650887519205025, 4800482495413153474, 17372223444201748306,
                           14562129569856756327, 17224433102950452784, 6291582168674905221, 14690815140091267338, 15416014634650931155, 5239947128529250534]
        assert poseidonminvar.perm_original(input_words) == expected_output, f"Standard permutation behaves differently from reference implementation."
        assert poseidonminvar(input_words) == expected_output, f"Enhanced permutation behaves differently from reference implementation."
        return True

def poseidonminvar_last_squeeze_poly_system(poseidonminvar, xs, hash_digest):
    t, R_F, R_P = poseidonminvar.t, poseidonminvar.R_F, poseidonminvar.R_P
    round_constants_field, MDS_matrix_field = poseidonminvar.round_constants_field, poseidonminvar.MDS_matrix_field
    num_rounds = R_F + R_P
    rate = len(hash_digest)
    cap = t - rate
    system = [xs[i + rate] - (xs[i] + round_constants_field[0][i])^3 for i in range(rate)] # ralating input and after-S-Box of first round # rate equations
    curr_state = [xs[i + rate] for i in range(rate)] + [round_constants_field[0][i]^3 for i in range(rate, t)] # state just before first MDS matrix
    curr_state = list(MDS_matrix_field * vector(curr_state)) # first (full) round complete
    xs_idx = 2*rate # index of next unused variable
    for r in range(1, num_rounds-1):
        curr_state = [curr_state[i] + round_constants_field[r][i] for i in range(t)]
        if r < (R_F // 2) or r >= (R_F // 2) + R_P: # full round
            curr_state = [curr_state[i]^3 for i in range(t)]
            system += [xs[xs_idx + i] - curr_state[i] for i in range(t)] # (R_F-2) * t equations
            curr_state = xs[xs_idx:xs_idx + t]
            xs_idx += t
        else: # partial round
            curr_state[0] = curr_state[0]^3
            system += [xs[xs_idx] - curr_state[0]] # R_P equations
            curr_state[0] = xs[xs_idx]
            xs_idx += 1
        curr_state = list(MDS_matrix_field * vector(curr_state))
    # last round
    curr_state = [curr_state[i] + round_constants_field[-1][i] for i in range(t)]
    curr_state = [curr_state[i]^3 for i in range(t)]
    curr_state = list(MDS_matrix_field * vector(curr_state))
    final_state = hash_digest + [0 for i in range(cap)]
    system += [final_state[i] - curr_state[i] for i in range(rate)] # r equations
    return system

def poseidonminvar_last_squeeze_trace(poseidonminvar, preimage):
    t, R_F, R_P = poseidonminvar.t, poseidonminvar.R_F, poseidonminvar.R_P
    round_constants_field, MDS_matrix_field = poseidonminvar.round_constants_field, poseidonminvar.MDS_matrix_field
    num_rounds = R_F + R_P
    rate = len(preimage)
    cap = t - rate
    state = matrix([preimage + [0]*cap]).transpose()
    trace = copy(preimage)
    # first round
    state += matrix([[round_constants_field[0][i] for i in range(t)]]).transpose()
    state = matrix([[el[0]^3 for el in state.rows()]]).transpose()
    trace += [el[0] for el in state.rows()[0:rate]]
    state = MDS_matrix_field * state
    # all other rounds but last
    for r in range(1, num_rounds-1):
        state += matrix([round_constants_field[r][i] for i in range(t)]).transpose()
        if r < (R_F // 2) or r >= (R_F // 2) + R_P: # full round
            state = matrix([el[0]^3 for el in state.rows()]).transpose()
            trace.extend(el[0] for el in state.rows())
        else:
            state[0,0] = state[0,0]^3
            trace.extend([state[0,0]])
        state = MDS_matrix_field * state
    # last round
    state += matrix([[round_constants_field[-1][i] for i in range(t)]]).transpose()
    state = matrix([el[0]^3 for el in state.rows()]).transpose()
    state = MDS_matrix_field * state
    digest = [el[0] for el in state.rows()[0:rate]]
    # trace.extend(el[0] for el in state.rows()[rate:t])
    return trace

def test_poseidonminvar_last_squeeze_poly_system():
    for prime, R_F, R_P, t, rate in [(65519, 2, 1, 3, 1), (11, 4, 1, 3, 1), (1021, 2, 2, 4, 3), (9973, 2, 0, 3, 2), (65519, 2, 0, 2, 1)]:
        cap = t - rate
        input_sequence = list(range(rate)) + [0]*cap
        poseidonminvar = Poseidon(prime=prime, R_F=R_F, R_P=R_P, t=t)
        hash_digest = poseidonminvar(input_sequence)[:rate]
        ring = PolynomialRing(GF(prime), 'x', t*(R_F-2) + R_P + rate + rate)
        print(ring)
        system = poseidonminvar_last_squeeze_poly_system(poseidonminvar, ring.gens(), hash_digest)
        trace = poseidonminvar_last_squeeze_trace(poseidonminvar, input_sequence[0:rate])
        for i in range(len(system)):
            p = system[i]
            assert not p(trace), f"The polynomial systen for PoseidonMinVar appears to be wrong in polynomial {i}: {p}"
        gb = Ideal(system).groebner_basis()
        assert not any([p(trace) for p in gb]), f"The Gröbner basis for PoseidonMinVar appears to be wrong."
    # Building the variety is generally too expensive. For the last set of parameters, it's okay, though.
    var = Ideal(gb).variety()
    assert trace in [list(el.values())[::-1] for el in var], f"The variety does not contain the intermediate values."
    return True



def poseidonmindeg_last_squeeze_poly_system(poseidon, xs, hash_digest):
    t, R_F, R_P = poseidon.t, poseidon.R_F, poseidon.R_P
    round_constants_field, MDS_matrix_field = poseidon.round_constants_field, poseidon.MDS_matrix_field
    num_rounds = R_F + R_P
    rate = len(hash_digest)
    cap = t - rate
    system = [xs[i + rate] - (xs[i] + round_constants_field[0][i])^3 for i in range(rate)] # ralating input and after-S-Box of first round # rate equations
    curr_state = [xs[i + rate] for i in range(rate)] + [round_constants_field[0][i]^3 for i in range(rate, t)] # state just before first MDS matrix
    curr_state = list(MDS_matrix_field * vector(curr_state)) # first (full) round complete
    xs_idx = 2*rate # index of next unused variable
    for r in range(1, num_rounds-1):
        curr_state = [curr_state[i] + round_constants_field[r][i] for i in range(t)]
        if r < (R_F // 2) or r >= (R_F // 2) + R_P: # full round
            curr_state = [curr_state[i]^3 for i in range(t)]
            system += [xs[xs_idx + i] - curr_state[i] for i in range(t)] # (R_F-2) * t equations
            curr_state = xs[xs_idx:xs_idx + t]
            xs_idx += t
        else: # partial round
            curr_state[0] = curr_state[0]^3
            system += [xs[xs_idx] - curr_state[0]] # R_P equations
            curr_state[0] = xs[xs_idx]
            xs_idx += 1
        curr_state = list(MDS_matrix_field * vector(curr_state))
    # last round
    curr_state = [curr_state[i] + round_constants_field[-1][i] for i in range(t)]
    curr_state = [curr_state[i]^3 for i in range(t)]
    final_state = hash_digest + [xs[xs_idx + i] for i in range(cap)]
    final_state = list(MDS_matrix_field.inverse() * vector(final_state))
    system += [final_state[i] - curr_state[i] for i in range(t)] # t equations
    return system

def poseidonmindeg_last_squeeze_trace(poseidon, preimage):
    t, R_F, R_P = poseidon.t, poseidon.R_F, poseidon.R_P
    round_constants_field, MDS_matrix_field = poseidon.round_constants_field, poseidon.MDS_matrix_field
    num_rounds = R_F + R_P
    rate = len(preimage)
    cap = t - rate
    state = matrix([preimage + [0]*cap]).transpose()
    trace = copy(preimage)
    # first round
    state += matrix([[round_constants_field[0][i] for i in range(t)]]).transpose()
    state = matrix([[el[0]^3 for el in state.rows()]]).transpose()
    trace += [el[0] for el in state.rows()[0:rate]]
    state = MDS_matrix_field * state
    # all other rounds but last
    for r in range(1, num_rounds-1):
        state += matrix([round_constants_field[r][i] for i in range(t)]).transpose()
        if r < (R_F // 2) or r >= (R_F // 2) + R_P: # full round
            state = matrix([el[0]^3 for el in state.rows()]).transpose()
            trace.extend(el[0] for el in state.rows())
        else:
            state[0,0] = state[0,0]^3
            trace.extend([state[0,0]])
        state = MDS_matrix_field * state
    # last round
    state += matrix([[round_constants_field[-1][i] for i in range(t)]]).transpose()
    state = matrix([el[0]^3 for el in state.rows()]).transpose()
    state = MDS_matrix_field * state
    digest = [el[0] for el in state.rows()[0:rate]]
    trace.extend(el[0] for el in state.rows()[rate:t])
    return trace

def test_poseidonmindeg_last_squeeze_poly_system():
    for prime, R_F, R_P, t, rate in [(65519, 2, 0, 2, 1), (101, 2, 1, 5, 3), (1021, 2, 2, 4, 3), (9973, 2, 2, 2, 1)]:
        cap = t - rate
        input_sequence = list(range(rate)) + [0]*cap
        poseidon = Poseidon(prime=prime, R_F=R_F, R_P=R_P, t=t)
        hash_digest = poseidon(input_sequence)[:rate]
        ring = PolynomialRing(GF(prime), 'x', t*R_F + R_P - cap)
        system = poseidonmindeg_last_squeeze_poly_system(poseidon, ring.gens(), hash_digest)
        trace = poseidonmindeg_last_squeeze_trace(poseidon, input_sequence[0:rate])
        for i in range(len(system)):
            p = system[i]
            assert not p(trace), f"The polynomial systen for Poseidon appears to be wrong in polynomial {i}: {p}"
        gb = Ideal(system).groebner_basis()
        assert not any([p(trace) for p in gb]), f"The Gröbner basis for Poseidon appears to be wrong."
    # Building the variety is generally too expensive. For the last set of parameters, it's okay, though.
    var = Ideal(gb).variety()
    assert trace in [list(el.values())[::-1] for el in var], f"The variety does not contain the intermediate values."
    return True
