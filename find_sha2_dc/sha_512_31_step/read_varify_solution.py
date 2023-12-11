import math


def handle(s):
    m = s.split(" = ")
    value = m[0].split("_")
    return value, m[1].replace("0b", "")


def get_result(find_str, array_len, data):
    data = data.replace("Invalid.\n", "").replace("ASSERT( ", "").replace(" );", "").replace("0b", "").split("\n")
    xr_0 = []
    xr_1 = []
    xr = []
    for i in range(array_len):
        temp_0 = []
        temp_1 = []
        temp = []
        for j in range(64):
            temp_0.append(0)
            temp_1.append(0)
            temp.append(0)
        xr_1.append(temp_1)
        xr_0.append(temp_0)
        xr.append(temp)
    for j in data:

        if find_str + "0_" in j and "b" not in j and "c" not in j and "temp" not in j:
            index, value = handle(j)
            xr_0[int(index[1])][int(index[2])] = value
        elif find_str + "1_" in j and "b" not in j and "c" not in j and "temp" not in j:
            index, value = handle(j)
            xr_1[int(index[1])][int(index[2])] = value
    for i in range(len(xr_0)):
        for j in range(64):
            if xr_0[i][j] == xr_1[i][j]:
                xr[i][j] = xr_1[i][j]
            elif xr_0[i][j] == "0" and xr_1[i][j] == "1":
                xr[i][j] = "u"
            elif xr_0[i][j] == "1" and xr_1[i][j] == "0":
                xr[i][j] = "n"
    for i in range(len(xr)):
        temp = "%2s:\""%i
        for j in range(63, -1, -1):
            temp += str(xr[i][j])
        temp += "\","
        print(temp)


if __name__ == '__main__':
    data = open("res2_varify_solution.out").read()
    print("second a")
    get_result("a", 28, data)
    print("second y")
    get_result("e", 28, data)
    print("second m")
    get_result("w", 28, data)

