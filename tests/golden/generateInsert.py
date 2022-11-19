import random as rand

N = 100_000
keys = [rand.randint(0, N) for _ in range(N)]
values = [rand.randint(0, N) for _ in range(N)]

keyToValue = {}
for key, value in zip(keys, values):
    keyToValue[key] = value

expected_range = list(map(lambda x: x[1], sorted(keyToValue.items())))
file_name = "stress_test_insert_1.golden"

open(file_name, "w").close()

with open(file_name, "a") as f:
    f.write(str(N) + '\n')
    f.write("\n".join(map(str, keys)) + "\n")
    f.write("\n".join(map(str, values)) + "\n")
    
    f.write("\n".join(map(str, expected_range)))
