import random as rand

N = 100_000

values = list(range(N))
rand.shuffle(values)
file_name = "stress_test_remove_3.golden"

open(file_name, "w").close()

with open(file_name, "a") as f:
    f.write("\n".join(map(str, values)) + "\n")
    
