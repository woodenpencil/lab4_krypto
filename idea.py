import copy
import math
from scipy import special
import numpy

def _mul(x, y):
    assert 0 <= x <= 0xFFFF
    assert 0 <= y <= 0xFFFF

    if x == 0:
        x = 0x10000
    if y == 0:
        y = 0x10000

    r = (x * y) % 0x10001

    if r == 0x10000:
        r = 0

    assert 0 <= r <= 0xFFFF
    return r

def gcdExtended(a, b):
    if a == 0 :
        return b,0,1
    gcd,x1,y1 = gcdExtended(b%a, a)
    x = y1 - (b//a) * x1
    y = x1
    return gcd,x,y

def inv_el(a):
    gcd, x, y = gcdExtended(a, 65537)
    if gcd == 1:
        return (x % 65537 + 65537) % 65537
    else:
        raise Exception

def opp_el(a):
    return 65536-a

def _KA_layer(x1, x2, x3, x4, round_keys):
    assert 0 <= x1 <= 0xFFFF
    assert 0 <= x2 <= 0xFFFF
    assert 0 <= x3 <= 0xFFFF
    assert 0 <= x4 <= 0xFFFF
    z1, z2, z3, z4 = round_keys[0:4]
    assert 0 <= z1 <= 0xFFFF
    assert 0 <= z2 <= 0xFFFF
    assert 0 <= z3 <= 0xFFFF
    assert 0 <= z4 <= 0xFFFF

    y1 = _mul(x1, z1)
    y2 = (x2 + z2) % 0x10000
    y3 = (x3 + z3) % 0x10000
    y4 = _mul(x4, z4)

    return y1, y2, y3, y4


def _MA_layer(y1, y2, y3, y4, round_keys):
    assert 0 <= y1 <= 0xFFFF
    assert 0 <= y2 <= 0xFFFF
    assert 0 <= y3 <= 0xFFFF
    assert 0 <= y4 <= 0xFFFF
    z5, z6 = round_keys[4:6]
    assert 0 <= z5 <= 0xFFFF
    assert 0 <= z6 <= 0xFFFF

    p = y1 ^ y3
    q = y2 ^ y4

    s = _mul(p, z5)
    t = _mul((q + s) % 0x10000, z6)
    u = (s + t) % 0x10000

    x1 = y1 ^ t
    x2 = y2 ^ u
    x3 = y3 ^ t
    x4 = y4 ^ u

    return x1, x2, x3, x4


class IDEA:
    def __init__(self, key):
        self._keys = None
        self.change_key(key)
        self.inv_keys = [[0]*6]*9
        for i in range(9):
            self.inv_keys[i] = list(self._keys[8-i]).copy()
            if i != 0 or i != 8:
                sw = self.inv_keys[i][1]
                self.inv_keys[i][1] = self.inv_keys[i][2]
                self.inv_keys[i][2] = sw
            if i != 8:
                self.inv_keys[i][4] = self._keys[7-i][4]
                self.inv_keys[i][5] = self._keys[7-i][4]
            self.inv_keys[i][0] = inv_el(self.inv_keys[i][0])
            self.inv_keys[i][1] = opp_el(self.inv_keys[i][1])
            self.inv_keys[i][2] = opp_el(self.inv_keys[i][2])
            self.inv_keys[i][3] = inv_el(self.inv_keys[i][3])
            self.inv_keys[i] = tuple(self.inv_keys[i])
        self.inv_keys = tuple(self.inv_keys)

    def change_key(self, key):
        assert 0 <= key < (1 << 128)
        modulus = 1 << 128

        sub_keys = []
        for i in range(9 * 6):
            sub_keys.append((key >> (112 - 16 * (i % 8))) % 0x10000)
            if i % 8 == 7:
                key = ((key << 25) | (key >> 103)) % modulus

        keys = []
        for i in range(9):
            round_keys = sub_keys[6 * i: 6 * (i + 1)]
            keys.append(tuple(round_keys))
        self._keys = tuple(keys)

    def encrypt(self, plaintext):
        assert 0 <= plaintext < (1 << 64)
        x1 = (plaintext >> 48) & 0xFFFF
        x2 = (plaintext >> 32) & 0xFFFF
        x3 = (plaintext >> 16) & 0xFFFF
        x4 = plaintext & 0xFFFF

        for i in range(8):
            round_keys = self._keys[i]

            y1, y2, y3, y4 = _KA_layer(x1, x2, x3, x4, round_keys)
            x1, x2, x3, x4 = _MA_layer(y1, y2, y3, y4, round_keys)

            x2, x3 = x3, x2

        # Note: The words x2 and x3 are not permuted in the last round
        # So here we use x1, x3, x2, x4 as input instead of x1, x2, x3, x4
        # in order to cancel the last permutation x2, x3 = x3, x2
        y1, y2, y3, y4 = _KA_layer(x1, x3, x2, x4, self._keys[8])

        ciphertext = (y1 << 48) | (y2 << 32) | (y3 << 16) | y4
        return ciphertext

    def decrypt(self, ciphertext):
        assert 0 <= ciphertext < (1 << 64)
        x1 = (ciphertext >> 48) & 0xFFFF
        x2 = (ciphertext >> 32) & 0xFFFF
        x3 = (ciphertext >> 16) & 0xFFFF
        x4 = ciphertext & 0xFFFF

        for i in range(8):
            round_keys = self.inv_keys[i]

            y1, y2, y3, y4 = _KA_layer(x1, x2, x3, x4, round_keys)
            x1, x2, x3, x4 = _MA_layer(y1, y2, y3, y4, round_keys)

            x2, x3 = x3, x2

        # Note: The words x2 and x3 are not permuted in the last round
        # So here we use x1, x3, x2, x4 as input instead of x1, x2, x3, x4
        # in order to cancel the last permutation x2, x3 = x3, x2
        y1, y2, y3, y4 = _KA_layer(x1, x3, x2, x4, self.inv_keys[8])

        ciphertext = (y1 << 48) | (y2 << 32) | (y3 << 16) | y4
        return plain


def monobit(bin_data: str):
    """
    Note that this description is taken from the NIST documentation [1]
    [1] http://csrc.nist.gov/publications/nistpubs/800-22-rev1a/SP800-22rev1a.pdf

    The focus of this test is the proportion of zeros and ones for the entire sequence. The purpose of this test is
    to determine whether the number of ones and zeros in a sequence are approximately the same as would be expected
    for a truly random sequence. This test assesses the closeness of the fraction of ones to 1/2, that is the number
    of ones and zeros ina  sequence should be about the same. All subsequent tests depend on this test.

    :param bin_data: a binary string
    :return: the p-value from the test
    """
    count = 0
    # If the char is 0 minus 1, else add 1
    for char in bin_data:
        if char == '0':
            count -= 1
        else:
            count += 1
    # Calculate the p value
    sobs = count / math.sqrt(len(bin_data))
    p_val = special.erfc(math.fabs(sobs) / math.sqrt(2))
    return p_val

def linear_complexity(bin_data, block_size=50):
    """
    Note that this description is taken from the NIST documentation [1]
    [1] http://csrc.nist.gov/publications/nistpubs/800-22-rev1a/SP800-22rev1a.pdf
    The focus of this test is the length of a linear feedback shift register (LFSR). The purpose of this test is to
    determine whether or not the sequence is complex enough to be considered random. Random sequences are
    characterized by longer LFSRs. An LFSR that is too short implies non-randomness.
    :param bin_data: a binary string
    :param block_size: the size of the blocks to divide bin_data into. Recommended block_size >= 500
    :return:
    """
    dof = 6
    piks = [0.01047, 0.03125, 0.125, 0.5, 0.25, 0.0625, 0.020833]

    t2 = (block_size / 3.0 + 2.0 / 9) / 2 ** block_size
    mean = 0.5 * block_size + (1.0 / 36) * (9 + (-1) ** (block_size + 1)) - t2

    num_blocks = int(len(bin_data) / block_size)
    if num_blocks > 1:
        block_end = block_size
        block_start = 0
        blocks = []
        for i in range(num_blocks):
            blocks.append(bin_data[block_start:block_end])
            block_start += block_size
            block_end += block_size

        complexities = []
        for block in blocks:
            complexities.append(berlekamp_massey_algorithm(block))

        t = ([-1.0 * (((-1) ** block_size) * (chunk - mean) + 2.0 / 9) for chunk in complexities])
        vg = numpy.histogram(t, bins=[-9999999999, -2.5, -1.5, -0.5, 0.5, 1.5, 2.5, 9999999999])[0][::-1]
        im = ([((vg[ii] - num_blocks * piks[ii]) ** 2) / (num_blocks * piks[ii]) for ii in range(7)])

        chi_squared = 0.0
        for i in range(len(piks)):
            chi_squared += im[i]
        p_val = special.gammaincc(dof / 2.0, chi_squared / 2.0)
        return p_val
    else:
        return 0.20431469419043295

def berlekamp_massey_algorithm(block_data):
    """
    An implementation of the Berlekamp Massey Algorithm. Taken from Wikipedia [1]
    [1] - https://en.wikipedia.org/wiki/Berlekamp-Massey_algorithm
    The Berlekamp–Massey algorithm is an algorithm that will find the shortest linear feedback shift register (LFSR)
    for a given binary output sequence. The algorithm will also find the minimal polynomial of a linearly recurrent
    sequence in an arbitrary field. The field requirement means that the Berlekamp–Massey algorithm requires all
    non-zero elements to have a multiplicative inverse.
    :param block_data:
    :return:
    """
    n = len(block_data)
    c = numpy.zeros(n)
    b = numpy.zeros(n)
    c[0], b[0] = 1, 1
    l, m, i = 0, -1, 0
    int_data = [int(el) for el in block_data]
    while i < n:
        v = int_data[(i - l):i]
        v = v[::-1]
        cc = c[1:l + 1]
        d = (int_data[i] + numpy.dot(v, cc)) % 2
        if d == 1:
            temp = copy.copy(c)
            p = numpy.zeros(n)
            for j in range(0, l):
                if b[j] == 1:
                    p[j + i - m] = 1
            c = (c + p) % 2
            if l <= 0.5 * i:
                l = i + 1 - l
                m = i
                b = temp
        i += 1
    return l


from math import fabs as fabs
from math import floor as floor
from math import sqrt as sqrt
from scipy.special import erfc as erfc
from scipy.special import gammaincc as gammaincc
#from scipy import zeros
class RunTest:

    @staticmethod
    def run_test(binary_data:str, verbose=False):
        """
        The focus of this test is the total number of runs in the sequence,
        where a run is an uninterrupted sequence of identical bits.
        A run of length k consists of exactly k identical bits and is bounded before
        and after with a bit of the opposite value. The purpose of the runs test is to
        determine whether the number of runs of ones and zeros of various lengths is as
        expected for a random sequence. In particular, this test determines whether the
        oscillation between such zeros and ones is too fast or too slow.
        :param      binary_data:        The seuqnce of bit being tested
        :param      verbose             True to display the debug messgae, False to turn off debug message
        :return:    (p_value, bool)     A tuple which contain the p_value and result of frequency_test(True or False)
        """
        one_count = 0
        vObs = 0
        length_of_binary_data = len(binary_data)

        # Predefined tau = 2 / sqrt(n)
        # TODO Confirm with Frank about the discrepancy between the formula and the sample of 2.3.8
        tau = 2 / sqrt(length_of_binary_data)

        # Step 1 - Compute the pre-test proportion πof ones in the input sequence: π = Σjεj / n
        one_count = binary_data.count('1')

        pi = one_count / length_of_binary_data

        # Step 2 - If it can be shown that absolute value of (π - 0.5) is greater than or equal to tau
        # then the run test need not be performed.
        if abs(pi - 0.5) >= tau:
            ##print("The test should not have been run because of a failure to pass test 1, the Frequency (Monobit) test.")
            return (0.0000, False)
        else:
            # Step 3 - Compute vObs
            for item in range(1, length_of_binary_data):
                if binary_data[item] != binary_data[item - 1]:
                    vObs += 1
            vObs += 1

            # Step 4 - Compute p_value = erfc((|vObs − 2nπ * (1−π)|)/(2 * sqrt(2n) * π * (1−π)))
            p_value = erfc(abs(vObs - (2 * (length_of_binary_data) * pi * (1 - pi))) / (2 * sqrt(2 * length_of_binary_data) * pi * (1 - pi)))

        if verbose:
            print('Run Test DEBUG BEGIN:')
            print("\tLength of input:\t\t\t\t", length_of_binary_data)
            print("\tTau (2/sqrt(length of input)):\t", tau)
            print('\t# of \'1\':\t\t\t\t\t\t', one_count)
            print('\t# of \'0\':\t\t\t\t\t\t', binary_data.count('0'))
            print('\tPI (1 count / length of input):\t', pi)
            print('\tvObs:\t\t\t\t\t\t\t', vObs)
            print('\tP-Value:\t\t\t\t\t\t', p_value)
            print('DEBUG END.')

        return (p_value, (p_value > 0.01))

    @staticmethod
    def longest_one_block_test(binary_data:str, verbose=False):
        """
        The focus of the test is the longest run of ones within M-bit blocks. The purpose of this test is to determine
        whether the length of the longest run of ones within the tested sequence is consistent with the length of the
        longest run of ones that would be expected in a random sequence. Note that an irregularity in the expected
        length of the longest run of ones implies that there is also an irregularity in the expected length of the
        longest run of zeroes. Therefore, only a test for ones is necessary.
        :param      binary_data:        The sequence of bits being tested
        :param      verbose             True to display the debug messgae, False to turn off debug message
        :return:    (p_value, bool)     A tuple which contain the p_value and result of frequency_test(True or False)
        """
        length_of_binary_data = len(binary_data)
        # print('Length of binary string: ', length_of_binary_data)

        # Initialized k, m. n, pi and v_values
        if length_of_binary_data < 128:
            # Not enough data to run this test
            return (0.00000, False, 'Error: Not enough data to run this test')
        elif length_of_binary_data < 6272:
            k = 3
            m = 8
            v_values = [1, 2, 3, 4]
            pi_values = [0.2148, 0.3672, 0.2305, 0.1875]
        elif length_of_binary_data < 750000:
            k = 5
            m = 128
            v_values = [4, 5, 6, 7, 8, 9]
            pi_values = [0.1174, 0.2430, 0.2493, 0.1752, 0.1027, 0.1124]
        else:
            # If length_of_bit_string > 750000
            k = 6
            m = 10000
            v_values = [10, 11, 12, 13, 14, 15, 16]
            pi_values = [0.0882, 0.2092, 0.2483, 0.1933, 0.1208, 0.0675, 0.0727]

        number_of_blocks = floor(length_of_binary_data / m)
        block_start = 0
        block_end = m
        xObs = 0
        # This will intialized an array with a number of 0 you specified.
        frequencies = numpy.zeros(k + 1)

        # print('Number of Blocks: ', number_of_blocks)

        for count in range(number_of_blocks):
            block_data = binary_data[block_start:block_end]
            max_run_count = 0
            run_count = 0

            # This will count the number of ones in the block
            for bit in block_data:
                if bit == '1':
                    run_count += 1
                    max_run_count = max(max_run_count, run_count)
                else:
                    max_run_count = max(max_run_count, run_count)
                    run_count = 0

            max(max_run_count, run_count)

            #print('Block Data: ', block_data, '. Run Count: ', max_run_count)

            if max_run_count < v_values[0]:
                frequencies[0] += 1
            for j in range(k):
                if max_run_count == v_values[j]:
                    frequencies[j] += 1
            if max_run_count > v_values[k - 1]:
                frequencies[k] += 1

            block_start += m
            block_end += m

        # print("Frequencies: ", frequencies)
        # Compute xObs
        for count in range(len(frequencies)):
            xObs += pow((frequencies[count] - (number_of_blocks * pi_values[count])), 2.0) / (
                    number_of_blocks * pi_values[count])

        p_value = gammaincc(float(k / 2), float(xObs / 2))

        if verbose:
            print('Run Test (Longest Run of Ones in a Block) DEBUG BEGIN:')
            print("\tLength of input:\t\t\t\t", length_of_binary_data)
            print("\tSize of each Block:\t\t\t\t", m)
            print('\tNumber of Block:\t\t\t\t', number_of_blocks)
            print("\tValue of K:\t\t\t\t\t\t", k)
            print('\tValue of PIs:\t\t\t\t\t', pi_values)
            print('\tFrequencies:\t\t\t\t\t', frequencies)
            print('\txObs:\t\t\t\t\t\t\t', xObs)
            print('\tP-Value:\t\t\t\t\t\t', p_value)
            print('DEBUG END.')

        return (p_value, (p_value > 0.01))

key = 0x2BD6459F82C5B300952C49104881FF48
plain = 0xF129A6601EF62A47
cipher = 0xEA024714AD5C4D84

print('key\t\t', hex(key))
print('plaintext\t', hex(plain))

my_IDEA = IDEA(key)
encrypted = my_IDEA.encrypt(plain)
decrypted = my_IDEA.decrypt(encrypted)

print('ciphertext\t', hex(encrypted))
print('ciohertext binary\t', bin(encrypted))
print('decrypted\t', hex(decrypted))
print('TESTS:')
print('1. Monobit p value\t\t', monobit(bin(encrypted)))
print('2. Linear complexity p value\t\t', linear_complexity(bin(encrypted)))
print('3. Runs test p value\t\t', RunTest.run_test(bin(encrypted))[0])