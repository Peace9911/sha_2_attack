import subprocess
from unit_function_512 import *


class FunctionModel:
    def __init__(self, init_HW, steps, bounds, message_bound, message_differential, op0, op1, op2, op3, op4, op5, op6,
                 op7):
        self.__obj_value = init_HW

        self.__end_step = bounds
        self.__start_step = steps
        self.__message_bound = message_bound
        self.__message_differential = message_differential
        self.__block_size = 64

        self.__declare = []
        self.__constraints = []

        self.__op0 = op0
        self.__op1 = op1
        self.__op2 = op2
        self.__op3 = op3
        self.__op4 = op4
        self.__op5 = op5
        self.__op6 = op6
        self.__op7 = op7

    def save_variable(self, s):
        temp = s + ": BITVECTOR(1);\n"
        if temp not in self.__declare:
            self.__declare.append(temp)
        return s

    def check_assign(self, s):
        if s not in self.__declare:
            self.__declare.append(s)

    def assign_value(self):
        for i in range(self.__message_bound):
            if i not in self.__message_differential:
                for j in range(self.__block_size):
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("wv_" + str(i) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("wd_" + str(i) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
        temp = "ASSERT BVGT(BVPLUS(10,"
        for i in range(len(self.__message_differential)):
            print(self.__message_differential[i])
            for j in range(self.__block_size):
                if len(self.__message_differential) - 1 == i and j == self.__block_size - 1:
                    temp += "0bin000000000@%s), 0bin%s);\n" % (
                        self.save_variable(
                            "wv_" + str(self.__message_differential[i]) + "_" + str(self.__block_size - 1 - j)),
                        bin(1)[2:].zfill(10))
                else:
                    temp += "0bin000000000@%s," % (
                        self.save_variable(
                            "wd_" + str(self.__message_differential[i]) + "_" + str(self.__block_size - 1 - j)))
        self.__constraints.append(temp)

        for step in range(self.__start_step - 4, self.__start_step):
            for i in range(self.__block_size):
                temp = "ASSERT xv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT xd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT yv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT yd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                self.__constraints.append(temp)
        for step in range(self.__end_step - 8, self.__end_step):
            for i in range(self.__block_size):
                temp = "ASSERT xv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT xd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                self.__constraints.append(temp)
        for step in range(self.__end_step - 4, self.__end_step):
            for i in range(self.__block_size):
                temp = "ASSERT yv_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                temp += "ASSERT yd_" + str(step) + "_" + str(i) + " = 0bin0;\n"
                self.__constraints.append(temp)
        aa = []
        for i in range(len(aa)):
            for j in range(len(aa[i])):
                if aa[i][j] == "=":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("xv_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("xd_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif aa[i][j] == "u":
                    temp = "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("xv_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("xd_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif aa[i][j] == "n":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("xv_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("xd_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
        aa = ["=n======nunnu==u=u=========u==uu=n=u========nnn====n=====u=u====",
              "===============================================================u",
              "========================n=======================================",
              "============u===========nu============n======================nuu"]
        for i in range(len(aa)):
            for j in range(len(aa[i])):
                if aa[i][j] == "=":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("xv_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("xd_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif aa[i][j] == "u":
                    temp = "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("xv_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("xd_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif aa[i][j] == "n":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("xv_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("xd_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
        ee = ["u=uu==u=n=nuu====nnu==uu=un=uu=u===un======nu=uu=n=======nn=uu=u",
              "==============u======u=n==n======n=====n==nu=un=n=n=====n=======",
              "==n===================unn=====u=====u=u=========================",
              "================u========n============n====u=========n=======nuu",
              "==u=======un==n=nn========u==un====unnn=n==n=========u==u=======",
              "============n============u============u========================u",
              "================================================================",
              "============u============n============n========================n"]
        for i in range(len(ee)):
            for j in range(len(ee[i])):
                if ee[i][j] == "=":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("yv_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("yd_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif ee[i][j] == "u":
                    temp = "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("yv_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("yd_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif ee[i][j] == "n":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("yv_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("yd_" + str(i + 7) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)

        ss = ["==n======n=====un======u=====u=nunnnnu======u=====nn=======u====",
              "n=u======u======n======n====un=============n====uu===u=u=nuuuuu=",
              "=u=============n============u====u==unn==n====u=======n========u",
              "n=====nu=====u=====nu=====n======u=====u======u=================",
              "============u============n============n========================n",
              "================================================================",
              "================================================================",
              "================================================================",
              "================================================================",
              "================================================================",
              "================================================================",
              "=======unnnnn====nuuuuuuuu=======nuuuuu================nuuuuuuuu",
              "================================================================",
              "============n============u============u========================u"]
        for i in range(len(ss)):
            for j in range(len(ss[i])):
                if ss[i][j] == "=":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("wv_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("wd_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif ss[i][j] == "u":
                    temp = "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("wv_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("wd_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)
                elif ss[i][j] == "n":
                    temp = "ASSERT %s = 0bin0;\n" % (
                        self.save_variable("wv_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    temp += "ASSERT %s = 0bin1;\n" % (
                        self.save_variable("wd_" + str(i + 5) + "_" + str(self.__block_size - 1 - j)))
                    self.__constraints.append(temp)

    def main(self):
        for i in range(self.__start_step, self.__end_step):
            variable_e, constrain_e = sha_e(self.__block_size, self.__op0[i], self.__op1[i], self.__op2[i], i)
            self.__constraints.append("".join(constrain_e))
            for var in variable_e:
                self.check_assign(var)
            variable_a, constrain_a = sha_a(self.__block_size, self.__op3[i], self.__op4[i], self.__op5[i], i)
            self.__constraints.append("".join(constrain_a))
            for var in variable_a:
                self.check_assign(var)
            if self.__op7[i] == 1:
                variable, constrain = sha2_value(self.__block_size, "IF", "MAJ", i)
                self.__constraints.append("".join(constrain))
                for var in variable:
                    self.check_assign(var)

        for i in range(self.__message_bound):
            if i > 15:
                variable_w, constrain_w = message_expand(self.__block_size, self.__op6[i], i)
                self.__constraints.append("".join(constrain_w))
                for var in variable_w:
                    self.check_assign(var)

    def obj_value(self, obj):
        temp = "ASSERT BVPLUS(10,"
        for i in range(self.__start_step, self.__end_step):
            for j in range(self.__block_size):
                if i == self.__end_step - 1 and j == self.__block_size - 1:
                    temp += "0bin000000000@%s) = 0bin%s;\n" % ("yd_" + str(i) + "_" + str(j), bin(obj)[2:].zfill(10))
                else:
                    temp += "0bin000000000@%s," % ("yd_" + str(i) + "_" + str(j))
        return temp

    def solver(self):
        self.main()
        self.assign_value()
        constrain = "".join(self.__constraints)
        variable = "".join(self.__declare)
        query = '\n' + 'QUERY FALSE;\nCOUNTEREXAMPLE;'
        kk = -1
        for obj_val in range(self.__obj_value, -1, -1):
            file_write = open("find_dc_model.cvc", "w")
            obj = self.obj_value(obj_val)
            file_write.write(variable)
            file_write.write(constrain)
            # file_write.write(obj)
            file_write.write(query)
            file_write.close()
            print("start solver")
            stp_parameters = ["stp", "find_dc_model.cvc", "--cryptominisat", "--threads", "26"]
            R = subprocess.check_output(stp_parameters)
            if "Valid.\n" != R.decode():
                file = open("res2_dc_solution_" + str(obj_val) + ".out", "w")
                file.write(R.decode())
                file.close()
                print("The number of HW in a differential characteristic is %s: valid" % obj_val)
                kk = obj_val

            else:
                print("The number of HW in a differential characteristic is %s: invalid" % obj_val)
                break
        if kk != -1:
            for temp in read_differential_characteristic(self.__block_size,
                                                         "res2_dc_solution_" + str(kk) + ".out",
                                                         self.__message_bound):
                for tt in temp:
                    print(tt)


if __name__ == '__main__':
    start_step = 5
    end_step = 19
    message_bound = 31
    init_HW = 60
    message_differential = [5, 6, 7, 8, 9, 16, 18]
    op0 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    op1 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    op2 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    op3 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    op4 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    op5 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    op6 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    op7 = [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    FunctionModel(init_HW, start_step, end_step, message_bound, message_differential, op0, op1, op2, op3, op4, op5, op6,
                  op7).solver()
