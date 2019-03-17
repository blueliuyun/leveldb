/* Copyright (c) 2011 The LevelDB Authors. All rights reserved.
   Use of this source code is governed by a BSD-style license that can be
   found in the LICENSE file. See the AUTHORS file for names of contributors. */

/** 
 * Compailer CMD :
 * Current Dir is : /home/tian/leveldb-master/db
 * $  g++ -std=c++11 -o test_open_write_read -g -I../include test_open_write_read.cc ../build/libleveldb.a -lpthread
*/
#include <assert.h>
#include <iostream>
#include "leveldb/db.h"

using namespace std;

int main()
{
  leveldb::DB* db = nullptr;
  leveldb::Options opts;

  // 如果打开已存在数据库的时候，需要抛出错误，将以下代码插在leveldb::DB::Open方法前面
  opts.create_if_missing = true;
  leveldb::Status status = leveldb::DB::Open(opts, "/tmp/testdb_tian_0317", &db);

  std::string key = "time_20190317_1557";
  std::string value_put = "value_20190317_1557";
  status = db->Put(leveldb::WriteOptions(), key, value_put);

  // 根据key查询value
  std::string value_get = "";
  status = db->Get(leveldb::ReadOptions(), key, &value_get);
  if (!status.ok()) {
    std::cerr << key << ": " << status.ToString() << std::endl;
  } else {
    std::cout << key << "==" << value_get << std::endl;
  }

  delete db;
  db = nullptr;
  return 0;
}