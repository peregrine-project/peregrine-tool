with open("xid_continue_ranges") as file:
    lines = [line.rstrip().split() for line in file]

def pp_codepoint(c):
    return f"(D{c[0]},(D{c[1]},(D{c[2]},(D{c[3]},(D{c[4]},D{c[5]})))))"

def pp_compare(r):
    return f"compare_range c {pp_codepoint(r[0])} {pp_codepoint(r[1])}"

def pp_match(lines):
    if len(lines) == 1:
        return f"(match {pp_compare(lines[0])} with | Eq => true | Gt => false | Lt => false end)"
    elif len(lines) == 0:
        return "false"
    else:
        n = len(lines)//2
        r = lines[n]
        low = lines[0:n]
        high = lines[n+1:]
    return f"(match {pp_compare(r)} with\n| Eq => true\n| Gt => {pp_match(low)}\n| Lt => {pp_match(high)}\nend)"




print(pp_match(lines))
