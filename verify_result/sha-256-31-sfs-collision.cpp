/**
 * SHA-256 implemented according to the specification:
 * http://csrc.nist.gov/publications/fips/fips180-4/fips-180-4.pdf
 */
#include <iomanip>
#include <iostream>
#include <sstream>
#include <vector>

typedef unsigned char BYTE;
typedef unsigned int WORD;
typedef unsigned long long ll;

// Constants used in hash algorithm
const WORD K[] = {0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
                  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
                  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
                  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
                  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};


std::vector<WORD> H; // Hashed message

WORD W[64]; // Message schedule

std::vector<WORD> hash_block(8);
// Working variables
WORD a, b, c, d, e, f, g, h;

// Temporary words
WORD T1, T2;

/**
 * Initialise the hash value.
 */
const void init_hash(WORD h0[])
{

    H.push_back(h0[0]);
    H.push_back(h0[1]);
    H.push_back(h0[2]);
    H.push_back(h0[3]);
    H.push_back(h0[4]);
    H.push_back(h0[5]);
    H.push_back(h0[6]);
    H.push_back(h0[7]);
}

/**
 * Rotate right function ROTR^n(x) in hash algorithm.
 */
const WORD ROTR(const WORD &n, const WORD &x)
{
    return (x >> n) | (x << (32 - n));
}

/**
 * Right shift function SHR^n(x) in hash algorithm.
 */
const WORD SHR(const WORD &n, const WORD &x)
{
    return x >> n;
}

/**
 * Logical function Ch(x, y, z) in hash algorithm.
 */
const WORD Ch(const WORD &x, const WORD &y, const WORD &z)
{
    return (x & y) ^ (~x & z);
}

/**
 * Logical function Maj(x, y, z) in hash algorithm.
 */
const WORD Maj(const WORD &x, const WORD &y, const WORD &z)
{
    return (x & y) ^ (x & z) ^ (y & z);
}

/**
 * Logical function (large) sigma^256_0(x) in hash algorithm.
 */
const WORD lsigma0(const WORD &x)
{
    return ROTR(2, x) ^ ROTR(13, x) ^ ROTR(22, x);
}

/**
 * Logical function (large) sigma^256_1(x) in hash algorithm.
 */
const WORD lsigma1(const WORD &x)
{
    return ROTR(6, x) ^ ROTR(11, x) ^ ROTR(25, x);
}

/**
 * Logical function (small) sigma^256_0(x) in hash algorithm.
 */
const WORD ssigma0(const WORD &x)
{
    return ROTR(7, x) ^ ROTR(18, x) ^ SHR(3, x);
}

/**
 * Logical function (small) sigma^256_1(x) in hash algorithm.
 */
const WORD ssigma1(const WORD &x)
{
    return ROTR(17, x) ^ ROTR(19, x) ^ SHR(10, x);
}

/**
 * Compute the hash value.
 */
const void compute_hash(std::vector<WORD> M)
{
    for (int t = 0; t <= 15; ++t)
        W[t] = M[t]; // M^i in spec
    for (int t = 16; t <= 63; ++t)
        W[t] = ssigma1(W[t - 2]) + W[t - 7] + ssigma0(W[t - 15]) + W[t - 16];

    // Initialise working variables with previous hash value
    a = H[0];
    b = H[1];
    c = H[2];
    d = H[3];
    e = H[4];
    f = H[5];
    g = H[6];
    h = H[7];

    // Perform logical operations
    for (int t = 0; t <= 30; ++t)
    {
        T1 = h + lsigma1(e) + Ch(e, f, g) + K[t] + W[t];
        T2 = lsigma0(a) + Maj(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + T1;
        d = c;
        c = b;
        b = a;
        a = T1 + T2;
    }

    // Compute intermediate hash values by assigning them to H^i
    hash_block[0] = a + H[0];
    hash_block[1] = b + H[1];
    hash_block[2] = c + H[2];
    hash_block[3] = d + H[3];
    hash_block[4] = e + H[4];
    hash_block[5] = f + H[5];
    hash_block[6] = g + H[6];
    hash_block[7] = h + H[7];
}

/**
 * Output the generated hash value as a hexadecimal string.
 */
const void output_hash()
{
    // Concatenate the final hash blocks
    for (int i = 0; i < 8; ++i)
        std::cout << std::hex << std::setw(8) << std::setfill('0') << hash_block[i] << " ";
    std::cout << std::endl;
}

int main()
{
    WORD h0[] = {0x5730070d, 0xe93e0eec, 0xa46f6190, 0x47c21930, 0x93bb2b66, 0x2df854ca, 0xeba1176e, 0x223f677b};
    std::vector<WORD> W0;
     W0.push_back(0xe3145e26);
    W0.push_back(0x31001aac);
    W0.push_back(0xae431764);
    W0.push_back(0xe012d22d);
    W0.push_back(0x61062082);
    W0.push_back(0xab9a80a1);
    W0.push_back(0x40001b8);
    W0.push_back(0x21cd69a);
    W0.push_back(0xb8808664);
    W0.push_back(0xf6825458);
    W0.push_back(0xf7c57698);
    W0.push_back(0x7859f1ba);
    W0.push_back(0xae02ad7);
    W0.push_back(0xbb2ceb47);
    W0.push_back(0x2fdfe92);
    W0.push_back(0x6a5c3cd9);

    // Set the inital hash value
    init_hash(h0);

    // Compute the hash value
    compute_hash(W0);

    // Output the generated hash value
    output_hash();

    std::vector<WORD> W1;

    W1.push_back(0xe3145e26);
    W1.push_back(0x31001aac);
    W1.push_back(0xae431764);
    W1.push_back(0xe012d22d);
    W1.push_back(0x61062082);
    W1.push_back(0xab9a70a7);
    W1.push_back(0x42089a9);
    W1.push_back(0x520c8c94);
    W1.push_back(0xe0819764);
    W1.push_back(0xf682d45c);
    W1.push_back(0xf7c57698);
    W1.push_back(0x7859f1ba);
    W1.push_back(0xae02ad7);
    W1.push_back(0xbb2ceb47);
    W1.push_back(0x2fdfe92);
    W1.push_back(0x6a5c3cd9);

    // Compute the hash value
    compute_hash(W1);

    // Output the generated hash value
    output_hash();
}