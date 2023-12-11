# -*- coding: utf-8 -*-
# @Time    : 2022 2022/7/6 13:51
# @Author  : liyx
# @Project : computer_pycharm
# @file_name :sha_256_test.py
import subprocess
import time

from constrain_condition import *


class sha2:
    def __init__(self, rounds, message):
        self.__rounds = rounds
        self.__message_rounds = message
        self.__declare = []  # save variable
        self.__constraints = []  # save constrain
        self.__assign = []  # save assign value variable
        self.__in_var_a_0 = []  # save A variable
        self.__in_var_a_1 = []
        self.__in_var_e_0 = []  # save E variable
        self.__in_var_e_1 = []
        self.__in_var_m_0 = []  # save message variable
        self.__in_var_m_1 = []
        self.__in_var_c = []  # save constant variable
        self.create_variable()

    def create_variable(self):
        for step in range(self.__rounds + 4):
            temp_0 = []
            temp_1 = []
            for i in range(32):
                temp_0.append("a0_" + str(step) + "_" + str(i))
                temp_1.append("a1_" + str(step) + "_" + str(i))
            self.__in_var_a_0.append(temp_0)
            self.__in_var_a_1.append(temp_1)
        for step in range(self.__message_rounds):
            temp = []
            for i in range(32):
                temp.append("c_" + str(step) + "_" + str(i))
            self.__in_var_c.append(temp)
        for step in range(self.__rounds + 4):
            temp_0 = []
            temp_1 = []
            for i in range(32):
                temp_0.append("e0_" + str(step) + "_" + str(i))
                temp_1.append("e1_" + str(step) + "_" + str(i))
            self.__in_var_e_0.append(temp_0)
            self.__in_var_e_1.append(temp_1)

        for m in range(self.__message_rounds):
            temp_0 = []
            temp_1 = []
            for i in range(32):
                temp_0.append("w0_" + str(m) + "_" + str(i))
                temp_1.append("w1_" + str(m) + "_" + str(i))
            self.__in_var_m_0.append(temp_0)
            self.__in_var_m_1.append(temp_1)

    def save_variable(self, s):
        temp = s + ": BITVECTOR(1);\n"
        if temp not in self.__declare:
            self.__declare.append(temp)
        return s

    def right_shift(self, order, num):
        return order[num:] + order[:num]

    def modadd(self, a, b, c, v):
        eqn = "%"
        eqn += " %s %s %s %s \n" % (a[0], b[0], c[0], v[0])
        self.__constraints.append(eqn)
        for i in range(32):
            temp = [self.save_variable(a[i]),
                    self.save_variable(b[i]),
                    self.save_variable(c[i]),
                    self.save_variable(v[i]),
                    self.save_variable(c[i + 1])]
            eqn = self.create_constraints(temp, modadd_model)
            self.__constraints.append(eqn)

    def create_constraints(self, X, propagation_trail):
        fun = []
        for maxterm in propagation_trail:
            temp = []
            for i in range(len(maxterm)):
                if maxterm[i] == '1':
                    temp.append('(' + '~' + X[i] + ')')
                elif maxterm[i] == '0':
                    temp.append(X[i])
            fun.append('(' + "|".join(temp) + ')')
        constrain = 'ASSERT ' + '&'.join(fun) + '=0bin1' + ';\n'
        return constrain

    def boolean(self, x0, x1, x2, out, fna):
        if fna == "MAJ":
            for i in range(32):
                temp = [self.save_variable(x0[i]),
                        self.save_variable(x1[i]),
                        self.save_variable(x2[i]),
                        self.save_variable(out[i])]
                eqn = self.create_constraints(temp, maj)
                self.__constraints.append(eqn)
        elif fna == "XOR":
            for i in range(32):
                temp = [self.save_variable(x0[i]),
                        self.save_variable(x1[i]),
                        self.save_variable(x2[i]),
                        self.save_variable(out[i])]
                eqn = self.create_constraints(temp, xor)
                self.__constraints.append(eqn)
        elif fna == "IF":
            for i in range(32):
                temp = [self.save_variable(x0[i]),
                        self.save_variable(x1[i]),
                        self.save_variable(x2[i]),
                        self.save_variable(out[i])]
                eqn = self.create_constraints(temp, ifx)
                self.__constraints.append(eqn)

    def R_r(self, fna0, fna1, a0, a1, a2, a3, a4, e0, e1, e2, e3, e4, m, c, step, num):
        in_var_b0 = []
        in_var_b1 = []
        in_var_b2 = []
        in_var_b3 = []
        in_var_b4 = []
        in_var_b5 = []
        in_var_b6 = []
        in_var_b7 = []
        in_var_b8 = []
        in_var_b9 = []
        for i in range(32):
            in_var_b0.append("b0" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b1.append("b1" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b2.append("b2" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b3.append("b3" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b4.append("b4" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b5.append("b5" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b6.append("b6" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b7.append("b7" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b8.append("b8" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b9.append("b9" + str(num) + "_" + str(step) + "_" + str(i))
        in_var_c0 = []
        in_var_c1 = []
        in_var_c2 = []
        in_var_c3 = []
        in_var_c4 = []
        in_var_c5 = []
        in_var_c6 = []
        in_var_c7 = []
        for i in range(33):
            in_var_c0.append("c0" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c1.append("c1" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c2.append("c2" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c3.append("c3" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c4.append("c4" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c5.append("c5" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c6.append("c6" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c7.append("c7" + str(num) + "_" + str(step) + "_" + str(i))
        eqn = "ASSERT %s = 0bin0;\n" % (in_var_c0[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c1[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c2[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c3[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c4[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c5[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c6[0])

        self.__constraints.append(eqn)
        self.boolean(self.right_shift(e3, 6), self.right_shift(e3, 11), self.right_shift(e3, 25), in_var_b0, "XOR")
        self.boolean(e3, e2, e1, in_var_b1, fna0)
        self.modadd(in_var_b0, in_var_b1, in_var_c0, in_var_b2)
        self.modadd(m, in_var_b2, in_var_c1, in_var_b3)
        self.modadd(c, in_var_b3, in_var_c2, in_var_b4)
        self.modadd(e0, in_var_b4, in_var_c3, in_var_b5)
        # computer ei
        self.modadd(a0, in_var_b5, in_var_c4, e4)
        # computer ai
        self.boolean(self.right_shift(a3, 2), self.right_shift(a3, 13), self.right_shift(a3, 22), in_var_b6, "XOR")
        self.boolean(a3, a2, a1, in_var_b7, fna1)
        self.modadd(in_var_b5, in_var_b6, in_var_c5, in_var_b8)
        self.modadd(in_var_b7, in_var_b8, in_var_c6, a4)

    def assign_value_e(self):
        x = ["================================",
             "================================",
             "================================",
             "================================",

             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "===0============================",
             "===1=========11=====11======0===",
             "unnn1=1110=0=0101==00011==11110=",
             "010n0n0111010nu01001un011n10n=10",
             "0101u1n=1n0n010=u0=11nuu=1u00=n1",
             "=100010000=0101=0===0010=10=1=0=",
             "=unn010000=1000011=00011==0=101=",
             "10110nuuuuuuuuu0u101un000010n111",
             "=111=0000000000=0=1=001111111=1=",
             "11001101101000000001nuuuuuuuu001",
             "010100unu000001001u1000110unn=n1",
             "1100111u00nn=100110=u1u00unn000n",
             "uuu1uuuu01000=110n000111101=0101",
             "000u0n1000101=0un01=1100=u11n000",
             "011100un0u001unnnn11000000001111",
             "=110=111=0===000=1=======1==1===",
             "=nuu==0110===00101=0110=====110=",
             "=000============================",
             "=111============================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================"]
        for step in range(self.__message_rounds):
            for i in range(32):
                eqn = "ASSERT %s = 0bin%s;\n" % (self.save_variable(self.__in_var_c[step][31 - i]),
                                                 bin(k_constant[step])[2:].zfill(32)[i])
                self.__constraints.append(eqn)

        for step in range(self.__rounds + 4):
            for i in range(32):
                if x[step][31 - i] == "n":
                    eqn = "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_e_0[step][i])
                    eqn += "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_e_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "u":
                    eqn = "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_e_0[step][i])
                    eqn += "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_e_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "=":
                    eqn = "ASSERT %s = %s;\n" % (self.save_variable(self.__in_var_e_0[step][i]),
                                                 self.save_variable(self.__in_var_e_1[step][i]))
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "1":
                    eqn = "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_e_0[step][i])
                    eqn += "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_e_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "0":
                    eqn = "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_e_0[step][i])
                    eqn += "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_e_1[step][i])
                    self.__assign.append(eqn)

    def assign_value_a(self):
        x = ["================================",
             "================================",
             "================================",
             "================================",

             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "===u============================",
             "==============n=u====u======n===",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "============================n===",
             "=======u=u=======u==============",
             "================================",
             "===n============================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================"]

        for step in range(self.__rounds + 4):
            for i in range(32):
                if x[step][31 - i] == "n":
                    eqn = "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_a_0[step][i])
                    eqn += "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_a_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "u":
                    eqn = "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_a_0[step][i])
                    eqn += "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_a_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "=":
                    eqn = "ASSERT %s = %s;\n" % (self.save_variable(self.__in_var_a_0[step][i]),
                                                 self.save_variable(self.__in_var_a_1[step][i]))
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "1":
                    eqn = "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_a_0[step][i])
                    eqn += "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_a_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "0":
                    eqn = "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_a_0[step][i])
                    eqn += "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_a_1[step][i])
                    self.__assign.append(eqn)

    def message_expand(self, in_w_0, in_w_1, in_w_2, in_w_3, temp_sigma1, temp_sigma0, out_w, num, step):
        in_var_b0 = []
        in_var_b1 = []
        in_var_b2 = []
        in_var_b3 = []

        for i in range(32):
            in_var_b0.append("b0w" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b1.append("b1w" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b2.append("b2w" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_b3.append("b3w" + str(num) + "_" + str(step) + "_" + str(i))

        in_var_c0 = []
        in_var_c1 = []
        in_var_c2 = []

        for i in range(33):
            in_var_c0.append("c0w" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c1.append("c1w" + str(num) + "_" + str(step) + "_" + str(i))
            in_var_c2.append("c2w" + str(num) + "_" + str(step) + "_" + str(i))

        eqn = "ASSERT %s = 0bin0;\n" % (in_var_c0[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c1[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c2[0])
        self.__constraints.append(eqn)

        self.boolean(self.right_shift(in_w_0, 17), self.right_shift(in_w_0, 19),
                     self.right_shift(in_w_0, 10)[:22] + temp_sigma1, in_var_b0, "XOR")

        self.boolean(self.right_shift(in_w_2, 7), self.right_shift(in_w_2, 18),
                     self.right_shift(in_w_2, 3)[:29] + temp_sigma0, in_var_b1, "XOR")
        self.modadd(in_var_b0, in_var_b1, in_var_c0, in_var_b2)
        self.modadd(in_w_1, in_var_b2, in_var_c1, in_var_b3)
        self.modadd(in_w_3, in_var_b3, in_var_c2, out_w)

    def main_R(self):

        for step in range(4, self.__rounds + 4):
            self.R_r("IF", "MAJ", self.__in_var_a_0[step - 4], self.__in_var_a_0[step - 3],
                     self.__in_var_a_0[step - 2], self.__in_var_a_0[step - 1], self.__in_var_a_0[step],
                     self.__in_var_e_0[step - 4], self.__in_var_e_0[step - 3], self.__in_var_e_0[step - 2],
                     self.__in_var_e_0[step - 1], self.__in_var_e_0[step], self.__in_var_m_0[step - 4],
                     self.__in_var_c[step - 4], step, 0)
            self.R_r("IF", "MAJ", self.__in_var_a_1[step - 4], self.__in_var_a_1[step - 3],
                     self.__in_var_a_1[step - 2], self.__in_var_a_1[step - 1], self.__in_var_a_1[step],
                     self.__in_var_e_1[step - 4], self.__in_var_e_1[step - 3], self.__in_var_e_1[step - 2],
                     self.__in_var_e_1[step - 1], self.__in_var_e_1[step], self.__in_var_m_1[step - 4],
                     self.__in_var_c[step - 4], step, 1)
        for step in range(self.__message_rounds):

            if step > 15:
                temp_sigma1_w0 = []
                temp_sigma1_w1 = []

                temp_sigma0_w0 = []
                temp_sigma0_w1 = []

                for i in range(10):
                    temp_sigma1_w0.append("tempsigma1w0" + "_" + str(step) + "_" + str(i))
                    temp_sigma1_w1.append("tempsigma1w1" + "_" + str(step) + "_" + str(i))
                for i in range(3):
                    temp_sigma0_w0.append("tempsigma0w0" + "_" + str(step) + "_" + str(i))
                    temp_sigma0_w1.append("tempsigma0w1" + "_" + str(step) + "_" + str(i))
                for i in range(10):
                    self.__constraints.append("ASSERT %s = 0bin0;\n" % (temp_sigma1_w0[i]))
                    self.__constraints.append("ASSERT %s = 0bin0;\n" % (temp_sigma1_w1[i]))
                for i in range(3):
                    self.__constraints.append("ASSERT %s = 0bin0;\n" % (temp_sigma0_w0[i]))
                    self.__constraints.append("ASSERT %s = 0bin0;\n" % (temp_sigma0_w1[i]))
                self.message_expand(self.__in_var_m_0[step - 2],
                                    self.__in_var_m_0[step - 7],
                                    self.__in_var_m_0[step - 15],
                                    self.__in_var_m_0[step - 16],
                                    temp_sigma1_w0,
                                    temp_sigma0_w0,
                                    self.__in_var_m_0[step],
                                    0, step)
                self.message_expand(self.__in_var_m_1[step - 2],
                                    self.__in_var_m_1[step - 7],
                                    self.__in_var_m_1[step - 15],
                                    self.__in_var_m_1[step - 16],
                                    temp_sigma1_w1,
                                    temp_sigma0_w1,
                                    self.__in_var_m_1[step],
                                    1, step)

    def assign_value_w(self):
        x = ["================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "===u============================",
             "======n===u==========u==========",
             "===n============================",
             "=======nn=======n===n===nn==uu=n",
             "=============u=======nn=========",
             "================================",
             "================================",
             "================================",
             "======n===u==========u==========",
             "===n============================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "=======n=n=======n==============",
             "================================",
             "===u============================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================",
             "================================"]

        for step in range(self.__message_rounds):
            for i in range(32):
                if x[step][31 - i] == "n":
                    eqn = "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_m_0[step][i])
                    eqn += "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_m_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "u":
                    eqn = "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_m_0[step][i])
                    eqn += "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_m_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "=":
                    eqn = "ASSERT %s = %s;\n" % (self.save_variable(self.__in_var_m_0[step][i]),
                                                 self.save_variable(self.__in_var_m_1[step][i]))
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "1":
                    eqn = "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_m_0[step][i])
                    eqn += "ASSERT %s = 0bin1;\n" % self.save_variable(self.__in_var_m_1[step][i])
                    self.__assign.append(eqn)
                elif x[step][31 - i] == "0":
                    eqn = "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_m_0[step][i])
                    eqn += "ASSERT %s = 0bin0;\n" % self.save_variable(self.__in_var_m_1[step][i])
                    self.__assign.append(eqn)

    def main(self):

        start = time.time()
        self.main_R()
        self.assign_value_a()
        self.assign_value_e()
        self.assign_value_w()
        query = '\n' + 'QUERY FALSE;\nCOUNTEREXAMPLE;'
        constrain = "".join(self.__constraints)
        assign = "".join(self.__assign)
        variable = "".join(self.__declare)
        file_write = open("varify_model.cvc", "w")
        file_write.write(variable)
        file_write.write(constrain)
        file_write.write(assign)
        file_write.write(query)
        file_write.close()
        print("start solver")
        stp_parameters = ["stp", "varify_model.cvc", "--cryptominisat", "--threads", "16"]
        R = subprocess.check_output(stp_parameters)
        print(R.decode())
        open("res2_varify_solution.out", "w").write(R.decode())
        print(time.time() - start)


if __name__ == '__main__':
    sha2(25, 39).main()
