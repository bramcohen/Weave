from difflib import SequenceMatcher
from copy import deepcopy
from struct import pack, unpack

class DiffCache:
    def __init__(self, filecache):
        self.filecache = filecache
        self.diffcache = {}

    def diff(self, a, b):
        assert a != b
        flipped = False
        if a < b:
            a, b = b, a
            flipped = True
        key = a + b
        if key in self.diffcache:
            r = self.diffcache[key]
        else:
            sm = SequenceMatcher()
            sm.set_seqs(self.filecache[a], self.filecache[b])
            r = sm.get_matching_blocks()
            self.diffcache[key] = r
        if flipped:
            return [(v2, v1, v3) for (v1, v2, v3) in r]
        else:
            return r

def WeaveCompactInner(history, snapshots, files):
    # history is [[ancestor id]]
    # snapshots is [{filename: filehash}]
    # files is {filehash: filedata}
    if not history:
        return [], {}
    files2 = {}
    for filehash, filedata in files.items():
        expanded = [x + b'\n' for x in filedata.split(b'\n')]
        if expanded:
            expanded[-1] = expanded[-1][:-1]
            if not expanded[-1]:
                del expanded[-1]
        files2[filehash] = expanded
    files = files2
    diffcache = DiffCache(files)
    # find the 'main' ancestor of each node by the one which has the smallest diff
    ancestors = [-1] * len(history)
    for c, cs in enumerate(history):
        if not cs:
            continue
        if len(cs) == 1:
            ancestors[c] = cs[0]
            continue
        best = None
        bestval = 2 ** 32
        for current in cs:
            currentval = 0
            for filename in set(snapshots[c].keys()):
                # Ideally resurrections wouldn't be counted as wholly new, 
                # but the we can't calculate it yet because we don't have the 
                # history ordering. Ressurections are unusual and this is 
                # just a heuristic anyway, so counted as new they are.
                if filename not in snapshots[current]:
                    currentval += len(files[snapshots[c][filename]])
                else:
                    va, vb = snapshots[c][filename], snapshots[current][filename]
                    if va != vb:
                        currentval += len(files[va]) + len(files[vb]) - 2 * sum([x[2] for x in diffcache.diff(va, vb)])
            if currentval < bestval:
                best = current
                bestval = currentval
        ancestors[c] = best
    # make the first element of each forwards array be the one with the longest path
    forwards = [[] for i in range(len(history)+1)]
    for x, y in enumerate(ancestors):
        forwards[y].append(x)
    depths = [None] * len(history)
    leaves = [x for x in range(len(ancestors)) if ancestors[x] != -1 and forwards[x] == []]
    while leaves:
        next = leaves.pop(-1)
        if next not in forwards:
            depths[next] = 0
        else:
            bestval, best = max((depths[x], x) for x in forwards[next])
            depths[next] = bestval + 1
            forwards[next].remove(best)
            forwards[next].insert(0, best)
        if next != -1 and all([x in depths for x in forwards[ancestors[next]]]):
            leaves.append(ancestors[next])
    # build the weave by starting at the root, then repeatedly traversing forwards and then 
    # backtracking as little as possible to a branch point
    # {filename: [(flips, line)]}
    weaves = {}
    snapshots = deepcopy(snapshots)
    commitid = forwards[-1][0]
    # [([(branch point, branch num)], pos)]
    positions = [None] * len(history)
    # [(branch point, branch num)]
    branches = []
    pos = 1
    while True:
        if ancestors[commitid] != -1:
            for filename in set(snapshots[ancestors[commitid]].keys()) - set(snapshots[commitid].keys()):
                snapshots[commitid][filename] = snapshots[ancestors[commitid]][filename]
        curpos = b''.join([pack('!LH', x, y) for x, y in branches]) + pack('!L', pos)
        curfull = pack('!H', len(curpos)) + curpos
        positions[commitid] = curpos
        for filename in list(snapshots[commitid].keys()):
            newsnap = files[snapshots[commitid][filename]]
            if filename not in weaves:
                weaves[filename] = [[curfull, x] for x in newsnap]
                continue
            if ancestors[commitid] != -1 and snapshots[commitid][filename] == snapshots[ancestors[commitid]][filename]:
                continue
            oldsnap = ([] if ancestors[commitid] == -1 else files[snapshots[ancestors[commitid]][filename]])
            oldpos = ('' if ancestors[commitid] == -1 else positions[ancestors[commitid]])
            weave = weaves[filename]
            pointbacks = []
            for weavepos, (flips, line) in enumerate(weave):
                include = False
                ps = 0
                while ps < len(flips):
                    nextlen = unpack('!H', flips[ps:ps + 2])[0]
                    ps += 2
                    if (nextlen <= len(oldpos) and flips[ps:ps + nextlen - 4] == oldpos[:nextlen-4] and 
                            unpack('!L', flips[ps + nextlen - 4:ps + nextlen])[0] <= 
                            unpack('!L', oldpos[nextlen - 4:nextlen])[0]):
                        include = not include
                    ps += nextlen
                if include:
                    assert oldsnap[len(pointbacks)] == line
                    pointbacks.append(weavepos)
            assert len(pointbacks) == len(oldsnap)
            # mark the lines which have been deleted
            mappings = ([(0, len(files[snapshots[commitid][filename]]), 0)] if ancestors[commitid] == -1 else 
                diffcache.diff(snapshots[ancestors[commitid]][filename], snapshots[commitid][filename]))
            ps = 0
            for indexa, indexb, length in mappings:
                for p in range(ps, indexa):
                    weave[pointbacks[p]][0] += curfull
                ps = indexa + length
            newweave = []
            weavepos = 0
            newsnappos = 0
            for mpos in range(len(mappings)):
                nextbegin = (len(weave) if mpos == len(mappings) - 1 else pointbacks[mappings[mpos][0]])
                weavesnip = weave[weavepos:nextbegin]
                newsnip = newsnap[newsnappos:mappings[mpos][1]]
                sm = SequenceMatcher()
                sm.set_seqs([x[1] for x in weavesnip], newsnip)
                snipmapping = sm.get_matching_blocks()
                weavesnippos = 0
                snippos = 0
                for snipmappos in range(len(snipmapping)):
                    clump = snipmapping[snipmappos]
                    newweave.extend([curfull, x] for x in newsnip[snippos:clump[1]])
                    newweave.extend(weavesnip[weavesnippos:clump[0]])
                    newweave.extend([[x + curfull, y] for x, y in weavesnip[clump[0]:clump[0] + clump[2]]])
                    snippos = clump[1] + clump[2]
                    weavesnippos = clump[0] + clump[2]
                newweave.extend([curfull, x] for x in newsnip[snippos:])
                newweave.extend(weavesnip[weavesnippos:])
                if mpos != len(mappings) - 1:
                    nextend = pointbacks[mappings[mpos][0] + mappings[mpos][2] - 1] + 1
                    newweave.extend(weave[nextbegin:nextend])
                    weavepos = nextend
                    newsnappos = mappings[mpos][1] + mappings[mpos][2]
            weaves[filename] = newweave
        if len(forwards[commitid]) != 0:
            commitid = forwards[commitid][0]
            pos += 1
        else:
            while True:
                if commitid == -1:
                    compactweaves = {}
                    for filename, weave in weaves.items():
                        compactweave = []
                        for ps, line in weave:
                            if compactweave and compactweave[-1][0] == ps:
                                compactweave[-1][1] += line
                            else:
                                compactweave.append([ps, line])
                        compactweaves[filename] = compactweave
                    return positions, {x: b''.join([pack('!H', len(flips)) + flips + 
                            pack('!H', len(line)) + line for (flips, line) in y]) for x, y in compactweaves.items()}
                commitid = ancestors[commitid]
                pos -= 1
                if pos < 0:
                    index = branches[-1][1] + 1
                    if index + 1 == len(forwards[commitid]):
                        pos = branches[-1][0]
                        del branches[-1]
                    else:
                        branches[-1] = (branches[-1][0], index)
                        commitid = forwards[commitid][index + 1]
                        pos = 0
                        break
                elif len(forwards[commitid]) > 1:
                    branches.append((pos, 0))
                    commitid = forwards[commitid][1]
                    pos = 0
                    break

def reconstruct(position, filehistory):
    result = []
    pos = 0
    while pos < len(filehistory):
        include = False
        flipend = pos + unpack('!H', filehistory[pos:pos + 2])[0]
        pos += 2
        while pos < flipend:
            nextlen = unpack('!H', filehistory[pos:pos+2])[0]
            pos += 2
            if (nextlen <= len(position) and filehistory[pos:pos + nextlen - 4] == position[:nextlen-4] and 
                    unpack('!L', filehistory[pos + nextlen - 4:pos + nextlen])[0] <= 
                    unpack('!L', position[nextlen - 4:nextlen])[0]):
                include = not include
            pos += nextlen
        nextlen = unpack('!H', filehistory[pos:pos + 2])[0]
        pos += 2
        if include:
            result.append(filehistory[pos:pos + nextlen])
        pos += nextlen
    return b''.join(result)

def get_all_positions(filehistory):
    result = set()
    pos = 0
    while pos < len(filehistory):
        flipend = pos + unpack('!H', filehistory[pos:pos + 2])[0]
        pos += 2
        while pos < flipend:
            nextlen = unpack('!H', filehistory[pos:pos+2])[0]
            pos += 2
            result.add(filehistory[pos:pos + nextlen])
            pos += nextlen
        nextlen = unpack('!H', filehistory[pos:pos + 2])[0]
        pos += 2 + nextlen
    return result

def WeaveCompact(history, snapshots, files):
    # history is {commit-id: [ancestor id]}
    # snapshots is {commit-id: {filename: filehash}}
    # files is {filehash: filedata}
    ids = list(snapshots.keys())
    lookups = {ident: pos for pos, ident in enumerate(ids)}
    history2 = [[lookups[y] for y in history.get(x, [])] for x in ids]
    snapshots2 = [snapshots[x] for x in ids]
    positions, filehistories = WeaveCompactInner(history2, snapshots2, files)
    return {ids[key]: val for (key, val) in enumerate(positions)}, filehistories

def test1():
    positions, weaves = WeaveCompact({'a': [], 'b': ['a']}, {'a': {'p': 'a'}, 'b': {'p': 'b'}}, {'a': 'line\nline2', 'b': 'line2\nline3'})
    assert set(weaves.keys()) == {'p'}
    assert set(get_all_positions(weaves['p'])) == set(positions.values())
    assert reconstruct(positions['a'], weaves['p']) == 'line\nline2'
    assert reconstruct(positions['b'], weaves['p']) == 'line2\nline3'

def test2():
    positions, weaves = WeaveCompact({}, {}, {})

def test3():
    positions, weaves = WeaveCompact({'a': [], 'b': ['a']}, {'a': {}, 'b': {}}, {})

def test4():
    positions, weaves = WeaveCompact({'a': [], 'b': [], 'c': [], 'd': ['a'], 'e': ['b', 'd', 'c']}, 
        {'a': {'p': 'a'}, 'b': {'p': 'b'}, 'c': {'p': 'c'}, 'd': {'p': 'd'}, 'e': {'p': 'e', 'q': 'f'}}, 
        {'a': 'line\nline2\n', 'b': 'line2\nline3\n', 'c': 'line3\nline2\nline4\n', 'd': 'line\nline3\n', 'e': 'line\nline3\nline2\n',
        'f': 'line'})
    assert set(weaves.keys()) == {'p', 'q'}
    assert set(get_all_positions(weaves['p'])) == set(positions.values())
    assert reconstruct(positions['a'], weaves['p']) == 'line\nline2\n'
    assert reconstruct(positions['b'], weaves['p']) == 'line2\nline3\n'
    assert reconstruct(positions['c'], weaves['p']) == 'line3\nline2\nline4\n'
    assert reconstruct(positions['d'], weaves['p']) == 'line\nline3\n'
    assert reconstruct(positions['e'], weaves['p']) == 'line\nline3\nline2\n'
    assert reconstruct(positions['e'], weaves['q']) == 'line'

def test_linear(versions):
    backlook = {}
    for i in range(len(versions)):
        backlook[versions[i]] = str(i)
    positions, weaves = WeaveCompact({i: ([] if i == 0 else [i-1]) for i in range(len(versions))},
        {i: ({'p': backlook[versions[i]]} if versions[i] is not None else {}) for i in range(len(versions))}, 
        {str(i): versions[i] for i in range(len(versions)) if versions[i] is not None})
    assert set(weaves.keys()) == {'p'}
    ps = sorted(list(get_all_positions(weaves['p'])))
    for i in range(len(versions)):
        if versions[i] is not None:
            assert reconstruct(positions[i], weaves['p']) == versions[i]

test1()
test2()
test3()
test4()
test_linear(['line1\nline2\nend', 'line0\nline1\nend', 'line1\nline2\nend'])
test_linear(['line1\n', '', 'line1\n', ''])
test_linear(['line1\nline2\n', 'linea\nline1\nline2\nline3\n'])
test_linear(['line1\nline2\n', None, '', 'line1\nline2\n', ''])
test_linear(['line1\n', '', 'line0\nline1\nline2\n', 'line1\nline2\nline0\n'])
