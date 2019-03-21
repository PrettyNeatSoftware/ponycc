
use "files"
use "ast"
use "collections"
use pc = "collections/persistent"

class val ResolveSourceFiles
  """
  This class is responsible for finding and loading *.pony source files.
  """
  let _auth: AmbientAuth
  let _search_paths: Array[String] val
  let _content_overrides: pc.Map[String, String] val
  
  new val create(
    auth': AmbientAuth,
    search_paths': Array[String] val = [],
    content_overrides': pc.Map[String, String] val)
  =>
    """
    Ambient authority is required so that the entire filesystem is available.

    The optional search_paths parameter will specify the global search paths
    to fall back to if a directory couldn't be found relative to the start path.
    """
    (_auth, _search_paths, _content_overrides) = (auth', search_paths', content_overrides')
  
  fun apply(start_path: String, path: String): (String, Sources)? =>
    """
    Given the path of a file or directory to start with, find a directory
    that exists relative to that starting path or one of the other search paths,
    and return all of the *.pony source files that exist in that directory,
    loaded into memory as Source objects, ready for parsing.

    If the start_path is not a directory, the directory containing that file
    will be used as the actual starting path for the search.
    """
    let dir_path = _find_dir(start_path, path)?
    let dir = Directory(dir_path)?
    let sources: Array[Source] trn = []
    for file_name in dir.entries()?.values() do
      if Path.ext(file_name) != "pony" then continue end

      let file_path = Path.join(dir_path.path, file_name)
      if _content_overrides.contains(file_path) then
        try
          sources.push(Source(_content_overrides(file_path)?, file_path))
          continue
        end
      end

      let file = dir.open_file(file_name)?

      if (file.errno() is FileOK) and (file.size() != -1) then
        let content = String.from_array(file.read(file.size()))
        sources.push(Source(content, file.path.path))
      end
    end
    (dir_path.path, consume sources)

  fun _find_dir(start_path: String, path: String): FilePath? =>
    """
    Given the path of a file or directory to start with, find a directory
    that exists relative to that starting path or one of the other search paths.

    If the start_path is not a directory, the directory containing that file
    will be used as the actual starting path for the search.
    """
    let all_search_paths = [start_path] .> concat(_search_paths.values())
    for search_path in all_search_paths.values() do
      try
        let dir_path = FilePath(_auth, Path.abs(
          if _is_dir(search_path) then
            Path.join(search_path, path)
          else
            Path.join(Path.dir(search_path), path)
          end
        ))?

        if _is_dir(dir_path.path) then return dir_path end
      else
        continue
      end
    end

    error

  fun _is_dir(path: String): Bool =>
    """
    Return true if the given path exists as a directory on the file system.
    """
    try FileInfo(FilePath(_auth, path)?)?.directory else false end
