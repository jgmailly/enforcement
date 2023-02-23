def is_credulously_accepted(argument, initial_extensions):
    for extension in initial_extensions:
        if argument in extension:
            return True
    return False

def is_skeptically_accepted(argument, initial_extensions):
    for extension in initial_extensions:
        if argument not in extension:
            return False
    return True
