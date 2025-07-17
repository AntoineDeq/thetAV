from thetAV import *
FF11 = GF(11)
FF = FF11.extension(int(16/FF11.factored_order()[0][1]), map=False)
FF.inject_variables()
thetAV.test_DeLu.test_change_level(1, 4, 8, FF11, FF)