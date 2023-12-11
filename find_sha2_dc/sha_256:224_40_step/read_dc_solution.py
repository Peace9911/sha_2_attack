def get_dc(data_list, step, find_str):
    data = data_list.replace("ASSERT( ", "").replace(" );", "").replace("\nInvalid.", "").split("\n")
    xv = []
    xd = []
    x = []
    for i in range(step):
        temp_v = []
        temp_d = []
        temp = []
        for j in range(32):
            temp_v.append(0)
            temp_d.append(0)
            temp.append(0)
        xv.append(temp_v)
        xd.append(temp_d)
        x.append(temp)
    for i in data:
        if find_str + "v" in i:
            index, value = handle(i)
            xv[int(index[1])][int(index[2])] = value
        elif find_str + "d" in i:
            index, value = handle(i)
            xd[int(index[1])][int(index[2])] = value
    for i in range(len(xv)):
        for j in range(32):
            if xv[i][j] == "1" and xd[i][j] == "1":
                x[i][j] = "u"
            elif xv[i][j] == "0" and xd[i][j] == "0":
                x[i][j] = "0"
            elif xv[i][j] != xd[i][j]:
                x[i][j] = "n"
    print(find_str + " differential")
    for i in range(len(x)):
        temp = "%2s\"" % i
        for j in range(31, -1, -1):
            if x[i][j] == "0":
                temp += "="
            elif x[i][j] == "u":
                temp += "u"
            elif x[i][j] == "n":
                temp += "n"
        temp += "\","
        print(temp)


def handle(s):
    temp = s.replace("0b", "").split(" = ")
    index = temp[0].split("_")
    return index, temp[1]

"""
this file can read message_dc.out,find_dc_model.out,res2_correct_solution_XX.out to obtain differential characteristic
"""
if __name__ == '__main__':
    data = open("right_res2_40_result_91.out", "r").read()
    get_dc(data, 40, "x")
    get_dc(data, 40, "y")
    get_dc(data, 40, "w")
