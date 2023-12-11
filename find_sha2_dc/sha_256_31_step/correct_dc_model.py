import subprocess

from constrain_condition import *


class FunctionModel:
    def __init__(self, steps, bounds, message_bound):

        self.__bounds_rounds = bounds
        self.__message_bound = message_bound
        self.__step = steps
        self.__declare = []  # save variable
        self.__constraints = []  # save constrains
        self.__assign = []  # save assign value

    def save_variable(self, s):
        temp = s + ": BITVECTOR(1);\n"
        if temp not in self.__declare:
            self.__declare.append(temp)
        return s

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

    def check_assign(self, s):
        if s not in self.__assign:
            self.__assign.append(s)

    def right_shift(self, order, num):
        return order[num:] + order[:num]

    def left_shift(self, order, num):
        """
        表示循环移位
        :param order:
        :param num:
        :return:
        """
        return order[-num:] + order[:-num]

    def xor_function(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v,
                     out_var_d, in_var_0, in_var_1, in_var_2):
        eqn = "% xor" + "%s model\n" % out_var_d[0]
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]),
                    self.save_variable(in_var_d_1[i]),
                    self.save_variable(in_var_v_2[i]),
                    self.save_variable(in_var_d_2[i]),
                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),
                    self.save_variable(in_var_0[i]),
                    self.save_variable(in_var_1[i]),
                    self.save_variable(in_var_2[i]),
                    ]
            eqn += self.create_constraints(temp, xor_full_constrain)
        self.__constraints.append(eqn)

    def if_function(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v, out_var_d,
                    in_var_0, in_var_1, in_var_2):
        eqn = ""
        for i in range(32):
            temp = [self.save_variable(in_var_v_1[i]),
                    self.save_variable(in_var_d_1[i]),
                    self.save_variable(in_var_v_2[i]),
                    self.save_variable(in_var_d_2[i]),
                    self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),
                    self.save_variable(in_var_1[i]),
                    self.save_variable(in_var_2[i]),
                    self.save_variable(in_var_0[i])
                    ]
            eqn += self.create_constraints(temp, ifz_full_constrain)
        self.__constraints.append(eqn)

    def maj_function(self, in_var_v_0, in_var_d_0, in_var_v_1, in_var_d_1, in_var_v_2, in_var_d_2, out_var_v, out_var_d,
                     in_var_0, in_var_1, in_var_2):
        eqn = ""
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]),
                    self.save_variable(in_var_d_1[i]),
                    self.save_variable(in_var_v_2[i]),
                    self.save_variable(in_var_d_2[i]),
                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),
                    self.save_variable(in_var_0[i]),
                    self.save_variable(in_var_1[i]),
                    self.save_variable(in_var_2[i])]
            eqn += self.create_constraints(temp, maj_full_constrain)
        self.__constraints.append(eqn)

    def expand_model(self, in_var_v, in_var_d, c_var_v, c_var_d, out_var_v, out_var_d, flag):

        eqn = "% expand_model\n"
        eqn += "ASSERT %s = 0bin0;\nASSERT %s = 0bin0;\n" % (c_var_v[0], c_var_d[0])
        if flag == 1:
            for i in range(32):
                temp = [self.save_variable(in_var_v[i]),
                        self.save_variable(in_var_d[i]),
                        self.save_variable(c_var_v[i]),
                        self.save_variable(c_var_d[i]),

                        self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(c_var_v[i + 1]),
                        self.save_variable(c_var_d[i + 1])]
                eqn += self.create_constraints(temp, expand_model_contsrain_1)
        else:
            for i in range(32):
                temp = [self.save_variable(out_var_v[i]),
                        self.save_variable(out_var_d[i]),
                        self.save_variable(in_var_v[i]),
                        self.save_variable(in_var_d[i]),
                        self.save_variable(c_var_v[i]),
                        self.save_variable(c_var_d[i]),
                        self.save_variable(c_var_v[i + 1]),
                        self.save_variable(c_var_d[i + 1])]
                eqn += self.create_constraints(temp, expand_model_contsrain_2)

        self.__constraints.append(eqn)

    def modadd_model(self, in_var_v_0, in_var_d_0,
                     in_var_v_1, in_var_d_1,
                     in_var_c_v, in_var_c_d,
                     out_var_v, out_var_d):
        eqn = "ASSERT %s = 0bin0;\n" % (in_var_c_v[0])
        eqn += "ASSERT %s = 0bin0;\n" % (in_var_c_d[0])
        for i in range(32):
            temp = [self.save_variable(in_var_v_0[i]),
                    self.save_variable(in_var_d_0[i]),
                    self.save_variable(in_var_v_1[i]),
                    self.save_variable(in_var_d_1[i]),
                    self.save_variable(in_var_c_v[i]),
                    self.save_variable(in_var_c_d[i]),
                    self.save_variable(out_var_v[i]),
                    self.save_variable(out_var_d[i]),
                    self.save_variable(in_var_c_v[i + 1]),
                    self.save_variable(in_var_c_d[i + 1])]
            eqn += self.create_constraints(temp, addexp_model_constrain)
        self.__constraints.append(eqn)

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

    def modadd(self, a, b, c, v):
        eqn = "ASSERT %s = 0bin0;\n" % (c[0])
        self.__constraints.append(eqn)
        for i in range(32):
            temp = [self.save_variable(a[i]),
                    self.save_variable(b[i]),
                    self.save_variable(c[i]),
                    self.save_variable(v[i]),
                    self.save_variable(c[i + 1])]
            eqn = self.create_constraints(temp, modadd_model)
            self.__constraints.append(eqn)

    def derive_cond(self, in_var_x, in_var_v_x, in_var_d_x):
        for i in range(32):
            temp = [self.save_variable(in_var_x[i]),
                    self.save_variable(in_var_v_x[i]),
                    self.save_variable(in_var_d_x[i])]
            eqn = self.create_constraints(temp, derive_cond_constrain)
            self.__constraints.append(eqn)

    def message_expand_value(self, in_var_v_w0, in_var_d_w0, in_var_v_w1, in_var_d_w1,
                             in_var_v_w2, in_var_d_w2, in_var_v_w3, in_var_d_w3,
                             in_var_v_w4, in_var_d_w4,
                             in_w_0, in_w_1, in_w_2, in_w_3,
                             temp_sigma1, temp_sigma0,
                             out_w, step):
        self.derive_cond(in_w_0, in_var_v_w0, in_var_d_w0)
        self.derive_cond(in_w_1, in_var_v_w1, in_var_d_w1)
        self.derive_cond(in_w_2, in_var_v_w2, in_var_d_w2)
        self.derive_cond(in_w_3, in_var_v_w3, in_var_d_w3)
        self.derive_cond(out_w, in_var_v_w4, in_var_d_w4)

        in_var_b0 = []
        in_var_b1 = []
        in_var_b2 = []
        in_var_b3 = []

        for i in range(32):
            in_var_b0.append("b0w" + "_" + str(step) + "_" + str(i))
            in_var_b1.append("b1w" + "_" + str(step) + "_" + str(i))
            in_var_b2.append("b2w" + "_" + str(step) + "_" + str(i))
            in_var_b3.append("b3w" + "_" + str(step) + "_" + str(i))

        in_var_c0 = []
        in_var_c1 = []
        in_var_c2 = []

        for i in range(33):
            in_var_c0.append("c0w" + "_" + str(step) + "_" + str(i))
            in_var_c1.append("c1w" + "_" + str(step) + "_" + str(i))
            in_var_c2.append("c2w" + "_" + str(step) + "_" + str(i))

        self.boolean(self.right_shift(in_w_0, 17), self.right_shift(in_w_0, 19),
                     self.right_shift(in_w_0, 10)[:22] + temp_sigma1, in_var_b0, "XOR")

        self.boolean(self.right_shift(in_w_2, 7), self.right_shift(in_w_2, 18),
                     self.right_shift(in_w_2, 3)[:29] + temp_sigma0, in_var_b1, "XOR")
        self.modadd(in_var_b0, in_var_b1, in_var_c0, in_var_b2)
        self.modadd(in_w_1, in_var_b2, in_var_c1, in_var_b3)
        self.modadd(in_w_3, in_var_b3, in_var_c2, out_w)

    def R_r(self, fna0, fna1, in_var_v_m, in_var_d_m,
            in_var_v_a0, in_var_d_a0, in_var_v_a1, in_var_d_a1,
            in_var_v_a2, in_var_d_a2, in_var_v_a3, in_var_d_a3, in_var_v_a4, in_var_d_a4,
            in_var_v_e0, in_var_d_e0, in_var_v_e1, in_var_d_e1,
            in_var_v_e2, in_var_d_e2, in_var_v_e3, in_var_d_e3, in_var_v_e4, in_var_d_e4,
            a0, a1, a2, a3, a4,
            e0, e1, e2, e3, e4,
            m, c, step):
        self.derive_cond(m, in_var_v_m, in_var_d_m)
        self.derive_cond(a0, in_var_v_a0, in_var_d_a0)
        self.derive_cond(a1, in_var_v_a1, in_var_d_a1)
        self.derive_cond(a2, in_var_v_a2, in_var_d_a2)
        self.derive_cond(a3, in_var_v_a3, in_var_d_a3)
        self.derive_cond(a4, in_var_v_a4, in_var_d_a4)

        self.derive_cond(e0, in_var_v_e0, in_var_d_e0)
        self.derive_cond(e1, in_var_v_e1, in_var_d_e1)
        self.derive_cond(e2, in_var_v_e2, in_var_d_e2)
        self.derive_cond(e3, in_var_v_e3, in_var_d_e3)
        self.derive_cond(e4, in_var_v_e4, in_var_d_e4)
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
            in_var_b0.append("b0" + "_" + str(step) + "_" + str(i))
            in_var_b1.append("b1" + "_" + str(step) + "_" + str(i))
            in_var_b2.append("b2" + "_" + str(step) + "_" + str(i))
            in_var_b3.append("b3" + "_" + str(step) + "_" + str(i))
            in_var_b4.append("b4" + "_" + str(step) + "_" + str(i))
            in_var_b5.append("b5" + "_" + str(step) + "_" + str(i))
            in_var_b6.append("b6" + "_" + str(step) + "_" + str(i))
            in_var_b7.append("b7" + "_" + str(step) + "_" + str(i))
            in_var_b8.append("b8" + "_" + str(step) + "_" + str(i))
            in_var_b9.append("b9" + "_" + str(step) + "_" + str(i))
        in_var_c0 = []
        in_var_c1 = []
        in_var_c2 = []
        in_var_c3 = []
        in_var_c4 = []
        in_var_c5 = []
        in_var_c6 = []
        in_var_c7 = []
        for i in range(33):
            in_var_c0.append("c0" + "_" + str(step) + "_" + str(i))
            in_var_c1.append("c1" + "_" + str(step) + "_" + str(i))
            in_var_c2.append("c2" + "_" + str(step) + "_" + str(i))
            in_var_c3.append("c3" + "_" + str(step) + "_" + str(i))
            in_var_c4.append("c4" + "_" + str(step) + "_" + str(i))
            in_var_c5.append("c5" + "_" + str(step) + "_" + str(i))
            in_var_c6.append("c6" + "_" + str(step) + "_" + str(i))
            in_var_c7.append("c7" + "_" + str(step) + "_" + str(i))

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

    def R(self, in_var_v_m, in_var_d_m, in_var_v_a0, in_var_d_a0, in_var_v_a1, in_var_d_a1, in_var_v_a2, in_var_d_a2,
          in_var_v_a3, in_var_d_a3, in_var_v_a4, in_var_d_a4, in_var_v_e0, in_var_d_e0, in_var_v_e1, in_var_d_e1,
          in_var_v_e2, in_var_d_e2, in_var_v_e3, in_var_d_e3, in_var_v_e4, in_var_d_e4, in_var_a0, in_var_a1, in_var_a2,
          in_var_a3, in_var_e0, in_var_e1, in_var_e2, in_var_e3, step):

        in_var_v_b = []
        in_var_d_b = []
        for i in range(10):
            temp_b_v = []
            temp_b_d = []
            for j in range(32):
                temp_b_v.append("bv" + str(i) + "_" + str(step) + "_" + str(j))
                temp_b_d.append("bd" + str(i) + "_" + str(step) + "_" + str(j))
            in_var_v_b.append(temp_b_v)
            in_var_d_b.append(temp_b_d)

        # Claim signed difference vectors ∇c of size 33.
        in_var_v_c = []
        in_var_d_c = []
        for i in range(8):
            temp_c_v = []
            temp_c_d = []
            for j in range(33):
                temp_c_v.append("cv" + str(i) + "_" + str(step) + "_" + str(j))
                temp_c_d.append("cd" + str(i) + "_" + str(step) + "_" + str(j))

            in_var_v_c.append(temp_c_v)
            in_var_d_c.append(temp_c_d)

        self.xor_function(self.right_shift(in_var_v_e3, 6), self.right_shift(in_var_d_e3, 6),
                          self.right_shift(in_var_v_e3, 11), self.right_shift(in_var_d_e3, 11),
                          self.right_shift(in_var_v_e3, 25), self.right_shift(in_var_d_e3, 25),
                          in_var_v_b[0], in_var_d_b[0],
                          self.right_shift(in_var_e3, 6),
                          self.right_shift(in_var_e3, 11),
                          self.right_shift(in_var_e3, 25))

        self.if_function(in_var_v_e3, in_var_d_e3,
                         in_var_v_e2, in_var_d_e2,
                         in_var_v_e1, in_var_d_e1,
                         in_var_v_b[1], in_var_d_b[1],
                         in_var_e3,
                         in_var_e2,
                         in_var_e1)

        self.modadd_model(in_var_v_e0, in_var_d_e0,
                          in_var_v_b[0], in_var_d_b[0],
                          in_var_v_c[0], in_var_d_c[0],
                          in_var_v_b[2], in_var_d_b[2])
        self.modadd_model(in_var_v_b[2], in_var_d_b[2],
                          in_var_v_b[1], in_var_d_b[1],
                          in_var_v_c[1], in_var_d_c[1],
                          in_var_v_b[3], in_var_d_b[3])
        self.modadd_model(in_var_v_m, in_var_d_m,
                          in_var_v_b[3], in_var_d_b[3],
                          in_var_v_c[2], in_var_d_c[2],
                          in_var_v_b[4], in_var_d_b[4])
        # computer Ei
        self.modadd_model(in_var_v_a0, in_var_d_a0,
                          in_var_v_b[4], in_var_d_b[4],
                          in_var_v_c[3], in_var_d_c[3],
                          in_var_v_b[5], in_var_d_b[5])

        if step > self.__bounds_rounds - 5:
            self.expand_model(in_var_v_b[5], in_var_d_b[5],
                              in_var_v_c[4], in_var_d_c[4],
                              in_var_v_e4, in_var_d_e4, 0)
        else:
            self.expand_model(in_var_v_b[5], in_var_d_b[5],
                              in_var_v_c[4], in_var_d_c[4],
                              in_var_v_e4, in_var_d_e4, 1)

        # computer Ai
        self.xor_function(self.right_shift(in_var_v_a3, 2), self.right_shift(in_var_d_a3, 2),
                          self.right_shift(in_var_v_a3, 13), self.right_shift(in_var_d_a3, 13),
                          self.right_shift(in_var_v_a3, 22), self.right_shift(in_var_d_a3, 22),
                          in_var_v_b[6], in_var_d_b[6],
                          self.right_shift(in_var_a3, 2),
                          self.right_shift(in_var_a3, 13),
                          self.right_shift(in_var_a3, 22))

        self.maj_function(in_var_v_a3, in_var_d_a3,
                          in_var_v_a2, in_var_d_a2,
                          in_var_v_a1, in_var_d_a1,
                          in_var_v_b[7], in_var_d_b[7],
                          in_var_a3,
                          in_var_a2,
                          in_var_a1)

        self.modadd_model(in_var_v_b[4], in_var_d_b[4],
                          in_var_v_b[6], in_var_d_b[6],
                          in_var_v_c[5], in_var_d_c[5],
                          in_var_v_b[8], in_var_d_b[8])

        self.modadd_model(in_var_v_b[8], in_var_d_b[8],
                          in_var_v_b[7], in_var_d_b[7],
                          in_var_v_c[6], in_var_d_c[6],
                          in_var_v_b[9], in_var_d_b[9])

        if step > self.__bounds_rounds - 9:
            self.expand_model(in_var_v_b[9], in_var_d_b[9],
                              in_var_v_c[7], in_var_d_c[7],
                              in_var_v_a4, in_var_d_a4, 0)
        else:
            self.expand_model(in_var_v_b[9], in_var_d_b[9],
                              in_var_v_c[7], in_var_d_c[7],
                              in_var_v_a4, in_var_d_a4, 1)

    def message_expand(self, in_var_v_w0, in_var_d_w0, in_var_v_w1, in_var_d_w1, in_var_v_w2, in_var_d_w2, in_var_v_w3,
                       in_var_d_w3, in_var_w0, in_var_w2, in_var_v_w4, in_var_d_w4, step):
        in_var_v_b0 = []
        in_var_d_b0 = []
        in_var_v_b1 = []
        in_var_d_b1 = []
        in_var_v_b2 = []
        in_var_d_b2 = []
        in_var_v_b3 = []
        in_var_d_b3 = []
        in_var_v_b4 = []
        in_var_d_b4 = []

        for i in range(32):
            in_var_v_b0.append("mv0" + "_" + str(step) + "_" + str(i))
            in_var_d_b0.append("md0" + "_" + str(step) + "_" + str(i))
            in_var_v_b1.append("mv1" + "_" + str(step) + "_" + str(i))
            in_var_d_b1.append("md1" + "_" + str(step) + "_" + str(i))
            in_var_v_b2.append("mv2" + "_" + str(step) + "_" + str(i))
            in_var_d_b2.append("md2" + "_" + str(step) + "_" + str(i))
            in_var_v_b3.append("mv3" + "_" + str(step) + "_" + str(i))
            in_var_d_b3.append("md3" + "_" + str(step) + "_" + str(i))
            in_var_v_b4.append("mv4" + "_" + str(step) + "_" + str(i))
            in_var_d_b4.append("md4" + "_" + str(step) + "_" + str(i))
        in_var_v_c0 = []
        in_var_d_c0 = []
        in_var_v_c1 = []
        in_var_d_c1 = []
        in_var_v_c2 = []
        in_var_d_c2 = []
        in_var_v_c3 = []
        in_var_d_c3 = []
        for i in range(33):
            in_var_v_c0.append("mcv0" + "_" + str(step) + "_" + str(i))
            in_var_d_c0.append("mcd0" + "_" + str(step) + "_" + str(i))
            in_var_v_c1.append("mcv1" + "_" + str(step) + "_" + str(i))
            in_var_d_c1.append("mcd1" + "_" + str(step) + "_" + str(i))
            in_var_v_c2.append("mcv2" + "_" + str(step) + "_" + str(i))
            in_var_d_c2.append("mcd2" + "_" + str(step) + "_" + str(i))
            in_var_v_c3.append("mcv3" + "_" + str(step) + "_" + str(i))
            in_var_d_c3.append("mcd3" + "_" + str(step) + "_" + str(i))
        temp_v0 = []
        temp_d0 = []
        temp_v1 = []
        temp_d1 = []
        temp_0 = []
        temp_1 = []
        for i in range(10):
            temp_v0.append("temp0v" + "_" + str(step) + "_" + str(i))
            temp_d0.append("temp0d" + "_" + str(step) + "_" + str(i))
            temp_0.append("temp0" + "_" + str(step) + "_" + str(i))
        for i in range(3):
            temp_v1.append("temp1v" + "_" + str(step) + "_" + str(i))
            temp_d1.append("temp1d" + "_" + str(step) + "_" + str(i))
            temp_1.append("temp1" + "_" + str(step) + "_" + str(i))

        self.xor_function(self.right_shift(in_var_v_w0, 17), self.right_shift(in_var_d_w0, 17),
                          self.right_shift(in_var_v_w0, 19), self.right_shift(in_var_d_w0, 19),
                          self.right_shift(in_var_v_w0, 10)[:22] + temp_v0,
                          self.right_shift(in_var_d_w0, 10)[:22] + temp_d0,
                          in_var_v_b0, in_var_d_b0,
                          self.right_shift(in_var_w0, 17),
                          self.right_shift(in_var_w0, 19),
                          self.right_shift(in_var_w0, 10)[:22] + temp_0)
        self.modadd_model(in_var_v_b0, in_var_d_b0,
                          in_var_v_w1, in_var_d_w1,
                          in_var_v_c0, in_var_d_c0,
                          in_var_v_b1, in_var_d_b1)
        self.xor_function(self.right_shift(in_var_v_w2, 7), self.right_shift(in_var_d_w2, 7),
                          self.right_shift(in_var_v_w2, 18), self.right_shift(in_var_d_w2, 18),
                          self.right_shift(in_var_v_w2, 3)[:29] + temp_v1,
                          self.right_shift(in_var_d_w2, 3)[:29] + temp_d1,
                          in_var_v_b2, in_var_d_b2,
                          self.right_shift(in_var_w2, 7),
                          self.right_shift(in_var_w2, 18),
                          self.right_shift(in_var_w2, 3)[:29] + temp_1)
        self.modadd_model(in_var_v_b1, in_var_d_b1,
                          in_var_v_b2, in_var_d_b2,
                          in_var_v_c1, in_var_d_c1,
                          in_var_v_b3, in_var_d_b3)
        self.modadd_model(in_var_v_b3, in_var_d_b3,
                          in_var_v_w3, in_var_d_w3,
                          in_var_v_c2, in_var_d_c2,
                          in_var_v_b4, in_var_d_b4)
        self.expand_model(in_var_v_b4, in_var_d_b4, in_var_v_c3, in_var_d_c3, in_var_v_w4, in_var_d_w4, 0)

    def assign_value(self):
        for i in range(self.__message_bound):
            temp = "ASSERT BVGE(BVPLUS(10,"
            for j in range(32):
                if j == 31:
                    temp += "0bin000000000@%s),0bin%s);\n" % (
                        "wd_" + str(i) + "_" + str(j), bin(0)[2:].zfill(10))
                else:
                    temp += "0bin000000000@%s," % ("wd_" + str(i) + "_" + str(j))
            self.__constraints.append(temp)

        for step in range(self.__message_bound):
            if step > 15:
                for i in range(10):
                    temp = "ASSERT %s = 0bin0;\n" % ("temp0v" + "_" + str(step) + "_" + str(i))
                    temp += "ASSERT %s = 0bin0;\n" % ("temp0d" + "_" + str(step) + "_" + str(i))
                    temp += "ASSERT %s = 0bin0;\n" % ("temp0" + "_" + str(step) + "_" + str(i))
                    self.__constraints.append(temp)
                for i in range(3):
                    temp = "ASSERT %s = 0bin0;\n" % ("temp1v" + "_" + str(step) + "_" + str(i))
                    temp += "ASSERT %s = 0bin0;\n" % ("temp1d" + "_" + str(step) + "_" + str(i))
                    temp += "ASSERT %s = 0bin0;\n" % ("temp1" + "_" + str(step) + "_" + str(i))
                    self.__constraints.append(temp)

        for i in range(0, 5):
            for j in range(32):
                temp = "ASSERT %s = 0bin0;\n" % (self.save_variable("wv_" + str(i) + "_" + str(31 - j)))
                temp += "ASSERT %s = 0bin0;\n" % (self.save_variable("wd_" + str(i) + "_" + str(31 - j)))
                self.__constraints.append(temp)

        for i in range(19, self.__message_bound):
            for j in range(32):
                temp = "ASSERT %s = 0bin0;\n" % (self.save_variable("wv_" + str(i) + "_" + str(31 - j)))
                temp += "ASSERT %s = 0bin0;\n" % (self.save_variable("wd_" + str(i) + "_" + str(31 - j)))
                self.__constraints.append(temp)
        aa = ["=============================n==",
              "================================",
              "================u===========un=="]
        for i in range(len(aa)):
            for j in range(len(aa[i])):
                if aa[i][j] == "=":
                    temp = "ASSERT xv_" + str(i + 8) + "_" + str(31 - j) + " = 0bin0;\n"
                    temp += "ASSERT xd_" + str(i + 8) + "_" + str(31 - j) + " = 0bin0;\n"
                    self.__constraints.append(temp)
                elif aa[i][j] == "n":
                    temp = "ASSERT xv_" + str(i + 8) + "_" + str(31 - j) + " = 0bin0;\n"
                    temp += "ASSERT xd_" + str(i + 8) + "_" + str(31 - j) + " = 0bin1;\n"
                    self.__constraints.append(temp)
                elif aa[i][j] == "u":
                    temp = "ASSERT xv_" + str(i + 8) + "_" + str(31 - j) + " = 0bin1;\n"
                    temp += "ASSERT xd_" + str(i + 8) + "_" + str(31 - j) + " = 0bin1;\n"
                    self.__constraints.append(temp)
        ee = ["=u==un=u========n===u========u==",
              "============================u===",
              "==n=uuuuu======un====unnnnnnn===",
              "===u====uu==================n===",
              "================n===========n===",
              "================================",
              "================u============u=="]
        for i in range(len(ee)):
            for j in range(len(ee[i])):
                if ee[i][j] == "=":
                    temp = "ASSERT yv_" + str(i + 8) + "_" + str(31 - j) + " = 0bin0;\n"
                    temp += "ASSERT yd_" + str(i + 8) + "_" + str(31 - j) + " = 0bin0;\n"
                    self.__constraints.append(temp)
                elif ee[i][j] == "n":
                    temp = "ASSERT yv_" + str(i + 8) + "_" + str(31 - j) + " = 0bin0;\n"
                    temp += "ASSERT yd_" + str(i + 8) + "_" + str(31 - j) + " = 0bin1;\n"
                    self.__constraints.append(temp)
                elif ee[i][j] == "u":
                    temp = "ASSERT yv_" + str(i + 8) + "_" + str(31 - j) + " = 0bin1;\n"
                    temp += "ASSERT yd_" + str(i + 8) + "_" + str(31 - j) + " = 0bin1;\n"
                    self.__constraints.append(temp)
            ss = ["================nuuu=========uu=",
                  "==========u=====u===u======n===u",
                  "=u=u=======n=====n=nu=n=====nun=",
                  "=u=nn==========u===u===u========",
                  "================u============u==",
                  "================================",
                  "================================",
                  "================================",
                  "================================",
                  "================================",
                  "================================",
                  "=============unnnunnnnnnnnnnnn==",
                  "================================",
                  "================n============n=="]
            for i in range(len(ss)):
                for j in range(len(ss[i])):
                    if ss[i][j] == "=":
                        temp = "ASSERT wv_" + str(i + 5) + "_" + str(31 - j) + " = 0bin0;\n"
                        temp += "ASSERT wd_" + str(i + 5) + "_" + str(31 - j) + " = 0bin0;\n"
                        self.__constraints.append(temp)
                    elif ss[i][j] == "n":
                        temp = "ASSERT wv_" + str(i + 5) + "_" + str(31 - j) + " = 0bin0;\n"
                        temp += "ASSERT wd_" + str(i + 5) + "_" + str(31 - j) + " = 0bin1;\n"
                        self.__constraints.append(temp)
                    elif ss[i][j] == "u":
                        temp = "ASSERT wv_" + str(i + 5) + "_" + str(31 - j) + " = 0bin1;\n"
                        temp += "ASSERT wd_" + str(i + 5) + "_" + str(31 - j) + " = 0bin1;\n"
                        self.__constraints.append(temp)

        for step in range(1, 5):
            for i in range(32):
                temp = "ASSERT xv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT xd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT yv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT yd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                self.__constraints.append(temp)
        for step in range(11, self.__bounds_rounds):
            for i in range(32):
                temp = "ASSERT xv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT xd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                self.__constraints.append(temp)
        for step in range(15, self.__bounds_rounds):
            for i in range(32):
                temp = "ASSERT yv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT yd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                self.__constraints.append(temp)

    def main(self):
        in_var_v_a = []
        in_var_d_a = []
        in_var_v_e = []
        in_var_d_e = []
        in_var_a = []
        in_var_e = []
        in_var_v_w = []
        in_var_d_w = []
        in_var_w = []
        for step in range(0, self.__bounds_rounds):
            temp_v_a = []
            temp_d_a = []
            temp_a = []
            for i in range(32):
                temp_v_a.append("xv_" + str(step) + "_" + str(i))
                temp_d_a.append("xd_" + str(step) + "_" + str(i))
                temp_a.append("x_" + str(step) + "_" + str(i))
            in_var_v_a.append(temp_v_a)
            in_var_d_a.append(temp_d_a)
            in_var_a.append(temp_a)
        for step in range(0, self.__bounds_rounds):
            temp_v_e = []
            temp_d_e = []
            temp_e = []
            for i in range(32):
                temp_v_e.append("yv_" + str(step) + "_" + str(i))
                temp_d_e.append("yd_" + str(step) + "_" + str(i))
                temp_e.append("y_" + str(step) + "_" + str(i))
            in_var_v_e.append(temp_v_e)
            in_var_d_e.append(temp_d_e)
            in_var_e.append(temp_e)

        for step in range(0, self.__message_bound):
            temp_v_w = []
            temp_d_w = []
            temp_w = []
            for i in range(32):
                temp_v_w.append("wv_" + str(step) + "_" + str(i))
                temp_d_w.append("wd_" + str(step) + "_" + str(i))
                temp_w.append("w_" + str(step) + "_" + str(i))
            in_var_v_w.append(temp_v_w)
            in_var_d_w.append(temp_d_w)
            in_var_w.append(temp_w)

        for i in range(self.__step, self.__bounds_rounds):
            self.R(in_var_v_w[i], in_var_d_w[i], in_var_v_a[i - 4], in_var_d_a[i - 4],
                   in_var_v_a[i - 3], in_var_d_a[i - 3], in_var_v_a[i - 2], in_var_d_a[i - 2],
                   in_var_v_a[i - 1], in_var_d_a[i - 1], in_var_v_a[i], in_var_d_a[i],
                   in_var_v_e[i - 4], in_var_d_e[i - 4], in_var_v_e[i - 3], in_var_d_e[i - 3],
                   in_var_v_e[i - 2], in_var_d_e[i - 2], in_var_v_e[i - 1], in_var_d_e[i - 1],
                   in_var_v_e[i], in_var_d_e[i], in_var_a[i - 4], in_var_a[i - 3], in_var_a[i - 2], in_var_a[i - 1],
                   in_var_e[i - 4], in_var_e[i - 3], in_var_e[i - 2], in_var_e[i - 1],
                   i)
            if i in [7, 8, 9, 10, 11, 12]:
                in_var_constant = []
                for j in range(32):
                    in_var_constant.append("constant_%s_%s" % (i, j))
                for j in range(32):
                    eqn = "ASSERT %s = 0bin%s;\n" % (self.save_variable(in_var_constant[31 - j]),
                                                     bin(k_constant[i])[2:].zfill(32)[j])
                    self.__constraints.append(eqn)
                self.R_r("IF", "MAJ", in_var_v_w[i], in_var_d_w[i],
                         in_var_v_a[i - 4], in_var_d_a[i - 4], in_var_v_a[i - 3], in_var_d_a[i - 3],
                         in_var_v_a[i - 2], in_var_d_a[i - 2], in_var_v_a[i - 1], in_var_d_a[i - 1],
                         in_var_v_a[i], in_var_d_a[i],
                         in_var_v_e[i - 4], in_var_d_e[i - 4], in_var_v_e[i - 3], in_var_d_e[i - 3],
                         in_var_v_e[i - 2], in_var_d_e[i - 2], in_var_v_e[i - 1], in_var_d_e[i - 1],
                         in_var_v_e[i], in_var_d_e[i],
                         in_var_a[i - 4], in_var_a[i - 3], in_var_a[i - 2], in_var_a[i - 1], in_var_a[i],
                         in_var_e[i - 4], in_var_e[i - 3], in_var_e[i - 2], in_var_e[i - 1], in_var_e[i],
                         in_var_w[i], in_var_constant, i)
        for i in range(self.__message_bound):
            if i > 15:
                self.message_expand(in_var_v_w[i - 2], in_var_d_w[i - 2],
                                    in_var_v_w[i - 7], in_var_d_w[i - 7],
                                    in_var_v_w[i - 15], in_var_d_w[i - 15],
                                    in_var_v_w[i - 16], in_var_d_w[i - 16],
                                    in_var_w[i - 2], in_var_w[i - 15],
                                    in_var_v_w[i], in_var_d_w[i], i)
                # temp_sigma1 = []
                # temp_sigma0 = []
                # for j in range(10):
                #     temp_sigma1.append("temp0" + "_" + str(i) + "_" + str(i))
                # for j in range(3):
                #     temp_sigma0.append("temp1" + "_" + str(i) + "_" + str(i))
                # self.message_expand_value(in_var_v_w[i - 2], in_var_d_w[i - 2],
                #                           in_var_v_w[i - 7], in_var_d_w[i - 7],
                #                           in_var_v_w[i - 15], in_var_d_w[i - 15],
                #                           in_var_v_w[i - 16], in_var_d_w[i - 16],
                #                           in_var_v_w[i], in_var_d_w[i],
                #                           in_var_w[i - 2],
                #                           in_var_w[i - 7],
                #                           in_var_w[i - 15],
                #                           in_var_w[i - 16],
                #                           temp_sigma1,
                #                           temp_sigma0,
                #                           in_var_w[i],
                #                           i)

    def obj_value(self, obj):
        temp = "ASSERT BVPLUS(10,"
        for i in range(5, 8):
            for j in range(32):
                if i == 7 and j == 31:
                    temp += "0bin000000000@%s) = 0bin%s;\n" % ("yd_" + str(i) + "_" + str(j), bin(obj)[2:].zfill(10))
                else:
                    temp += "0bin000000000@%s," % ("yd_" + str(i) + "_" + str(j))
        return temp

    def solver(self):
        self.main()
        self.assign_value()
        constrain = "".join(self.__constraints)
        assign = "".join(self.__assign)
        variable = "".join(self.__declare)
        query = '\n' + 'QUERY FALSE;\nCOUNTEREXAMPLE;'
        for obj_val in range(30, -1, -1):
            file_write = open("correct_model.cvc", "w")
            obj = self.obj_value(obj_val)
            file_write.write(variable)
            file_write.write(constrain)
            file_write.write(assign)
            file_write.write(obj)
            file_write.write(query)
            file_write.close()
            print("start solver")
            stp_parameters = ["stp", "correct_model.cvc", "--cryptominisat", "--threads", "26"]
            R = subprocess.check_output(stp_parameters)
            if "Valid.\n" != R.decode():
                file = open("res2_correct_solution_" + str(obj_val) + ".out", "w")
                file.write(R.decode())
                file.close()
                print("The number of HW in a differential characteristic is %s: valid" % obj_val)
            else:
                print("The number of HW in a differential characteristic is %s: invalid" % obj_val)
                break


if __name__ == '__main__':
    step = 5
    bounds = 19
    message_bound = 31
    FunctionModel(step, bounds, message_bound).solver()
