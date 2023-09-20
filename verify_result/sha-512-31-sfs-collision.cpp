#include <algorithm>
#include <cmath>
#include <cstdio>
#include <ios>
#include <iostream>

#include <ctime>
#include <ostream>
#include <random>
#include <string>
using namespace std;
const unsigned long long EXP[64] = {
    0x1, 0x2, 0x4, 0x8,
    0x10, 0x20, 0x40, 0x80,
    0x100, 0x200, 0x400, 0x800,
    0x1000, 0x2000, 0x4000, 0x8000,
    0x10000, 0x20000, 0x40000, 0x80000,
    0x100000, 0x200000, 0x400000, 0x800000,
    0x1000000, 0x2000000, 0x4000000, 0x8000000,
    0x10000000, 0x20000000, 0x40000000, 0x80000000,
    0x100000000, 0x200000000, 0x400000000, 0x800000000,
    0x1000000000, 0x2000000000, 0x4000000000, 0x8000000000,
    0x10000000000, 0x20000000000, 0x40000000000, 0x80000000000,
    0x100000000000, 0x200000000000, 0x400000000000, 0x800000000000,
    0x1000000000000, 0x2000000000000, 0x4000000000000, 0x8000000000000,
    0x10000000000000, 0x20000000000000, 0x40000000000000, 0x80000000000000,
    0x100000000000000, 0x200000000000000, 0x400000000000000, 0x800000000000000,
    0x1000000000000000, 0x2000000000000000, 0x4000000000000000, 0x8000000000000000};
const uint64_t words[] = {
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817};

uint64_t RR(uint64_t x, unsigned int n)
{
    return (x >> n) | (x << (64 - n));
}
uint64_t ch(uint64_t e, uint64_t f, uint64_t g)
{
    return (e & f) ^ ((~e) & g);
}
uint64_t maj(uint64_t a, uint64_t b, uint64_t c)
{
    return (a & b) ^ (a & c) ^ (b & c);
}
uint64_t s0(uint64_t x)
{
    return RR(x, 1) ^ RR(x, 8) ^ (x >> 7);
}
uint64_t s1(uint64_t x)
{
    return RR(x, 19) ^ RR(x, 61) ^ (x >> 6);
}
uint64_t S0(uint64_t x)
{
    return RR(x, 28) ^ RR(x, 34) ^ RR(x, 39);
}
uint64_t S1(uint64_t x)
{
    return RR(x, 14) ^ RR(x, 18) ^ RR(x, 41);
}
inline unsigned long long getBit(unsigned int number, int position)
{
    return (number >> position) & 0x1;
}
uint64_t getValue(string str)
{
    uint64_t newValue = 0;
    for (int i = 0; i < 64; i++)
    {
        if (str[i] == 'n')
        {
            newValue = newValue + EXP[63 - i];
        }
        if (str[i] == '1')
        {
            newValue += EXP[63 - i];
        }
    }
    return newValue;
}
string toBinary(unsigned long long num)
{
    string str = "";
    unsigned long long left = 0;
    int array[64];
    for (int i = 0; i < 64; i++)
    {
        array[i] = 0;
    }
    int count = 0;
    while (num)
    {
        left = num % 2;
        array[count++] = left;
        num = num / 2;
    }

    for (int i = 63; i >= 0; i--)
    {
        // cout << array[i];
        if (array[i] == 1)
        {
            str += '1';
        }
        else
        {
            str += '0';
        }
        if (i % 4 == 0)
        {
            // cout << "";
            // str += ' ';
        }
    }

    return str;
}
string compare(uint64_t m0, uint64_t m1)
{
    string m0_temp = toBinary(m0);

    string m1_temp = toBinary(m1);
    string result = toBinary(0xffffffffffffffff);
    for (int i = 63; i >= 0; i--)
    {
        if (m0_temp[i] == m1_temp[i])
        {
            result[i] = '=';
        }
        else if (m0_temp[i] == '1' && m1_temp[i] == '0')
        {
            result[i] = 'n';
        }
        else if (m0_temp[i] == '0' && m1_temp[i] == '1')
        {
            result[i] = 'u';
        }
    }
    // cout <<"res:"<<result<<endl;
    return result;
}
uint64_t messaget_expand(uint64_t condition[], int num_rounds)
{
    return s1(condition[num_rounds - 2]) + s0(condition[num_rounds - 15]) + condition[num_rounds - 7] +
           condition[num_rounds - 16];
}
void compress39(uint64_t *e_condition, uint64_t *a_condition, uint64_t *W, int rounds,
                uint64_t *h)
{
    for (int i = 0; i < rounds - 16; i++)
    {
        W[16 + i] = messaget_expand(W, 16 + i);
    }

    for (int i = 4; i < rounds + 4; i++)
    {
        uint64_t inter_variable = e_condition[i - 4] + S1(e_condition[i - 1]) + ch(e_condition[i - 1], e_condition[i - 2], e_condition[i - 3]) + W[i - 4] + words[i - 4];
        e_condition[i] = a_condition[i - 4] + inter_variable;
        a_condition[i] =
            S0(a_condition[i - 1]) + inter_variable +
            maj(a_condition[i - 1], a_condition[i - 2], a_condition[i - 3]);
    }
    h[0] = a_condition[rounds + 3] + a_condition[3];
    h[1] = a_condition[rounds + 2] + a_condition[2];
    h[2] = a_condition[rounds + 1] + a_condition[1];
    h[3] = a_condition[rounds + 0] + a_condition[0];

    h[4] = e_condition[rounds + 3] + e_condition[3];
    h[5] = e_condition[rounds + 2] + e_condition[2];
    h[6] = e_condition[rounds + 1] + e_condition[1];
    h[7] = e_condition[rounds + 0] + e_condition[0];
}
int main()
{
    uint64_t a0_condition[43];
    uint64_t e0_condition[43];
    uint64_t a1_condition[43];
    uint64_t e1_condition[43];
    uint64_t W0[39];
    uint64_t W1[39];
    uint64_t h0[8];
    uint64_t h1[8];
    for (int i = 0; i < 39; i++)
    {
        W0[i] = 0;
        W1[i] = 0;
    }
    for (int i = 0; i < 43; i++)
    {
        a1_condition[i] = 0;
        e1_condition[i] = 0;
        a0_condition[i] = 0;
        e0_condition[i] = 0;
    }
    a0_condition[0] = 0x6dd99e5934fa4c36;
    a0_condition[1] = 0xd67789b44900bbd3;
    a0_condition[2] = 0xb99d911402b6f13b;
    a0_condition[3] = 0xe8db5ea7aa921652;

    a1_condition[0] = 0x6dd99e5934fa4c36;
    a1_condition[1] = 0xd67789b44900bbd3;
    a1_condition[2] = 0xb99d911402b6f13b;
    a1_condition[3] = 0xe8db5ea7aa921652;

    e0_condition[0] = 0x377be3bbc9ee6a9;
    e0_condition[1] = 0x6624b6d94833584f;
    e0_condition[2] = 0xb5ab5d050736da3;
    e0_condition[3] = 0x22c1b11afc030cd;

    e1_condition[0] = 0x377be3bbc9ee6a9;
    e1_condition[1] = 0x6624b6d94833584f;
    e1_condition[2] = 0xb5ab5d050736da3;
    e1_condition[3] = 0x22c1b11afc030cd;

    W0[0] = 0xc84e359a94cfa415;
    W0[1] = 0x8b62e2794d50178a;
    W0[2] = 0xcc95cf1218bc494a;
    W0[3] = 0x404e263440;
    W0[4] = 0x4b1c2f410a70233a;
    W0[5] = 0x2568946b7b20f000;
    W0[6] = 0x8e82c5955ff61841;
    W0[7] = 0x857f82c3b6494b6c;
    W0[8] = 0xc272b2af2a91b091;
    W0[9] = 0xa209a722f595461;
    W0[10] = 0x958e7d6a665ca726;
    W0[11] = 0xb82d422e9e59e3e3;
    W0[12] = 0x62188a13372b78d5;
    W0[13] = 0x74c63ff27970c;
    W0[14] = 0x810031ff62c060a;
    W0[15] = 0xc007835890369005;

    int rounds = 31;
    compress39(e0_condition, a0_condition, W0, rounds, h0);
    W1[0] = 0xc84e359a94cfa415;
    W1[1] = 0x8b62e2794d50178a;
    W1[2] = 0xcc95cf1218bc494a;
    W1[3] = 0x404e263440;
    W1[4] = 0x4b1c2f410a70233a;
    W1[5] = 0x529156e8728c010;
    W1[6] = 0x2ec244995fe6dd3f;
    W1[7] = 0xc57e82cbf80b496d;
    W1[8] = 0x4176aa8f6b93b091;
    W1[9] = 0xa289a322d595460;
    W1[10] = 0x958e7d6a665ca726;
    W1[11] = 0xb82d422e9e59e3e3;
    W1[12] = 0x62188a13372b78d5;
    W1[13] = 0x74c63ff27970c;
    W1[14] = 0x810031ff62c060a;
    W1[15] = 0xc007835890369005;
    compress39(e1_condition, a1_condition, W1, rounds, h1);
    for (int i = 0; i < 8; i++)
    {
        cout << hex << h0[i] << " ";
    }
    cout << endl;
    for (int i = 0; i < 8; i++)
    {
        cout << hex << h1[i] << " ";
    }
    cout << endl;

    // b22e20576043e9e4 74ec094a73c2a4b2 768e697e705bf85f 83f4d4de4c4eb0d5 54dc962fc2c73568 f83bf017e9e1f7d7 8e7cf3e30c956b29 638c85bc39044143
    return 0;
}